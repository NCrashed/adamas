/* Названный отказ вместо сигнала 11, когда стек исчерпан (§6, §10 вопрос 192).
 *
 * # Зачем он есть
 *
 * Гарантия §6 накрывает хвостовой вызов, у которого прототип вызываемого
 * дословно совпал с прототипом вызывающего. Применение **значения-функции** в
 * хвостовой позиции под неё не попадает и не попадёт: между вызывающим и кодом
 * замыкания стоит `adamas_apply`, у которого свой прототип, а граница замыкания
 * вдобавок боксирует (§4.11, решение 158), то есть после применения остаётся
 * работа и хвостовой позиции у него в C нет вовсе. Цикл такой формы поэтому
 * растит стек и рано или поздно его исчерпывает.
 *
 * До этого файла исчерпание выглядело сигналом 11 - «Ошибка сегментирования»,
 * без единого слова о причине. Правила проекта (§2.1) называют панику от
 * валидной программы серьёзным дефектом; отказ, который **называет** себя, -
 * не лечение, но и не сигнал.
 *
 * # Чего он стоит горячему пути
 *
 * Ничего. Обработчик ставится раз, при входе в программу, и до обращения к
 * памяти за границей стека не исполняется ни одной инструкции. Стоит он двух
 * системных вызовов на старте (`sigaltstack`, `sigaction`) и 64 КиБ статической
 * памяти под свой стек - обычную ловушку переполнения так и ставят: на кадре
 * исчерпанного стека обработчику работать негде.
 *
 * # Что он не накрывает, и это названо
 *
 * *Стек рабочего потока* (§5.2, `ADAMAS_THREADS`). Границы считаются от кадра,
 * с которого зовут `adamas_stack_guard`, то есть от главного потока; у
 * порождённого потока стек лежит в другом месте, и обращение туда под правило
 * не попадёт. Там остаётся прежний сигнал.
 *
 * *Чужая сторона* (§5.3). Переполнение внутри библиотеки, позванной через
 * границу, случится на нашем стеке и назовётся этим отказом - хотя виноват
 * будет не язык. Различить их нечем: адрес обращения говорит о стеке, а не о
 * том, чей кадр его исчерпал.
 *
 * *Обращение мимо стека* правилу не подчиняется вовсе: обработчик возвращает
 * сигналу умолчание и даёт обращению повториться, то есть дефект памяти
 * по-прежнему роняет процесс так, как ронял. Глушить чужой SIGSEGV своим
 * сообщением было бы хуже сигнала.
 */

/* Объявления POSIX прячет `-std=c11`: он просит строгий ISO, а `sigaction`,
 * `sigaltstack` и `getrlimit` живут за отметкой. Стоит она **до** включений и
 * только здесь - прочим файлам рантайма хватает ISO плюс `pthread.h`. */
#ifndef _POSIX_C_SOURCE
#    define _POSIX_C_SOURCE 200809L
#endif
/* `sigaltstack` и `SA_ONSTACK` - XSI, и одной отметки POSIX им мало. */
#ifndef _XOPEN_SOURCE
#    define _XOPEN_SOURCE 700
#endif
#if defined(__APPLE__) && !defined(_DARWIN_C_SOURCE)
#    define _DARWIN_C_SOURCE 1
#endif

#include "adamas.h"

/* Правило это POSIX'ово целиком - `sigaltstack` с `SA_ONSTACK`, - и на Windows
 * у него аналога нет ни одного. Символ там остаётся, чтобы `main.c` звал одно
 * и то же везде, а исчерпание стека возвращается к тому, чем было. */
#if defined(_WIN32)

void adamas_stack_guard(void) {}

#else

#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <sys/resource.h>
#include <unistd.h>

/* Свой стек обработчика. Размер числом, а не `SIGSTKSZ`: с glibc 2.34 тот
 * перестал быть константой времени трансляции и статический массив им не
 * размерить. 64 КиБ - с запасом: обработчик ниже не зовёт ничего, кроме
 * `write` и `_exit`. */
#define ADAMAS_GUARD_BYTES 65536u

/* Допуск на обе границы: страница-страж, округление `RLIMIT_STACK` и кадры
 * между `main` и точкой замера. Мегабайт - грубо и намеренно: ошибиться в
 * сторону «назвал стеком чужой адрес» дешевле, чем промолчать о своём. */
#define ADAMAS_STACK_SLACK ((uintptr_t)1u << 20)

/* Код возврата названного отказа. Отличается и от успеха, и от сигнала. */
#define ADAMAS_STACK_EXIT 3

static char adamas_guard_bytes[ADAMAS_GUARD_BYTES];

/* Верх стека: адрес кадра, с которого ставился обработчик. */
static uintptr_t adamas_stack_ceiling;

/* Низ: верх минус `RLIMIT_STACK`. */
static uintptr_t adamas_stack_floor;

static const char adamas_stack_message[] =
    "adamas: стек исчерпан. Гарантирован хвостовой вызов, у которого прототип "
    "вызываемого совпал с прототипом вызывающего (§6); применение "
    "значения-функции в хвостовой позиции гарантии не имеет и растит стек "
    "(§10 вопрос 192).\n";

/* Обращение за границу: назвать причину и уйти, либо вернуть сигналу умолчание. */
static void adamas_stack_fault(int signo, siginfo_t *info, void *context) {
    uintptr_t at = info != NULL ? (uintptr_t)info->si_addr : 0;
    struct sigaction back;
    (void)context;
    if (at + ADAMAS_STACK_SLACK >= adamas_stack_floor
        && at <= adamas_stack_ceiling + ADAMAS_STACK_SLACK) {
        /* Только `write` и `_exit`: всё прочее в обработчике незаконно. */
        ssize_t said = write(2, adamas_stack_message, sizeof adamas_stack_message - 1);
        (void)said;
        _exit(ADAMAS_STACK_EXIT);
    }
    back.sa_handler = SIG_DFL;
    sigemptyset(&back.sa_mask);
    back.sa_flags = 0;
    (void)sigaction(signo, &back, NULL);
}

void adamas_stack_guard(void) {
    struct rlimit limit;
    stack_t area;
    struct sigaction caught;
    char here = 0;
    /* Умолчание на случай `RLIM_INFINITY`: восемь мегабайт - то, что ставит
     * `ulimit -s` почти везде. Ошибка здесь стоит только ширины окна. */
    uintptr_t span = (uintptr_t)8u << 20;

    (void)here;
    if (getrlimit(RLIMIT_STACK, &limit) == 0 && limit.rlim_cur != RLIM_INFINITY
        && limit.rlim_cur > 0) {
        span = (uintptr_t)limit.rlim_cur;
    }
    adamas_stack_ceiling = (uintptr_t)&here;
    adamas_stack_floor = adamas_stack_ceiling > span ? adamas_stack_ceiling - span : 0;

    area.ss_sp = adamas_guard_bytes;
    area.ss_size = sizeof adamas_guard_bytes;
    area.ss_flags = 0;
    if (sigaltstack(&area, NULL) != 0) {
        /* Своего стека нет - ставить обработчик нельзя: он упал бы там же, где
         * упала программа, и сигнал вышел бы тот же, только двумя кадрами
         * позже. */
        return;
    }
    caught.sa_sigaction = adamas_stack_fault;
    sigemptyset(&caught.sa_mask);
    caught.sa_flags = SA_SIGINFO | SA_ONSTACK;
    (void)sigaction(SIGSEGV, &caught, NULL);
    /* macOS отвечает на исчерпание стека то SIGSEGV, то SIGBUS - берутся оба. */
    (void)sigaction(SIGBUS, &caught, NULL);
}

#endif /* !_WIN32 */
