//! `ThreadSanitizer` над счётчиком разделяемого значения (§5.1).
//!
//! # Зачем инструмент, если рядом уже есть стенд
//!
//! `tests/atomic.rs` ловит **случившуюся** гонку: пропавшую инкрементацию видно
//! числом. Планировщик, однако, вправе развести потоки так, что перекрытия не
//! будет вовсе, и тогда тот стенд зеленеет на сломанном коде. Санитайзер ловит
//! саму **возможность**: несинхронизированную пару доступов он назовёт и там,
//! где число сошлось.
//!
//! # Чем стенд держится честным
//!
//! Проверку проверяют мутантом, как всякую другую: рядом с честным прогоном
//! стоит **ломаный**, который считает счётчик голым `header->rc += 1` в обход
//! рантайма. Заголовок объекта в `adamas.h` открыт, поэтому написать такое
//! можно прямо в стенде, не трогая рантайм. Санитайзер обязан назвать гонку у
//! ломаного и промолчать у честного; промолчи он у обоих - инструмент не
//! включился, и тест это скажет, а не пройдёт.
//!
//! *Что проверка напечатает, если сломать проверяемое.* Сними `lock` с
//! инкрементации рантайма - и честный прогон начнёт печатать `data race` на
//! `adamas_dup`. Именно эта строка и есть наблюдаемое.
//!
//! # Границы
//!
//! Санитайзер не ловит того, чего программа не сделала: он видит **исполненные**
//! пары доступов. Стенд поэтому гоняет тот же ряд операций, что гонял бы
//! `spawn`, - взятие, отдачу и вопрос об уникальности, - на одном разделяемом
//! объекте из нескольких потоков.
//!
//! # Второй стенд: транзитивность промоушена
//!
//! Тот же инструмент отвечает и на вопрос §5.2 - доходит ли пометка до
//! **достижимого**. Потоки там трогают ребёнка разделяемой головы, а ломаная
//! половина есть прежняя реализация дословно: помечен один объект. Настоящих
//! потоков для этого не понадобилось, и это главное, что стенд показывает:
//! различать транзитивный промоушен умеет уже `pthread_create`.
//!
//! Собирается стенд `ADAMAS_CC`; если он не умеет `-fsanitize=thread`, тест
//! говорит об этом и не проверяет ничего. Молчаливого пропуска нет.

#![allow(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::Command;

/// Общая шапка стенда: объект, потоки, ход.
const HARNESS: &str = r#"
#include "adamas.h"
#include <pthread.h>
#include <stdio.h>

#define THREADS 4
#define ROUNDS 20000

static adamas_value target;

static void *walk(void *arg) {
    (void)arg;
    for (int round = 0; round < ROUNDS; round += 1) {
        TAKE;
        GIVE;
    }
    return NULL;
}

int main(void) {
    pthread_t threads[THREADS];
    target = adamas_alloc(0, 1);
    adamas_set_field(target, 0, adamas_imm(1));
    MARK;
    for (int at = 0; at < THREADS; at += 1) {
        pthread_create(&threads[at], NULL, walk, NULL);
    }
    for (int at = 0; at < THREADS; at += 1) {
        pthread_join(threads[at], NULL);
    }
    printf("rc=%u unique=%d\n", adamas_rc(target), adamas_is_unique(target));
    adamas_drop(target, NULL);
    printf("live=%zu\n", adamas_stat_live_everywhere());
    return 0;
}
"#;

/// Стенд транзитивного промоушена: потоки трогают **ребёнка** разделяемого.
///
/// Форма захвата взята из §5.2 дословно: `spawn` получает одно значение, а
/// поток работает со всем, до чего из него доходит, - так делает всякий разбор
/// списка, дупающий хвост. Ходы здесь только взятия: отдай их поток тут же, и
/// счётчик ломаного стенда уводил бы объект в смерть посреди чужой ссылки, то
/// есть стенд падал бы в `malloc` прежде, чем санитайзер договорит.
const NESTED: &str = r#"
#include "adamas.h"
#include <pthread.h>
#include <stdio.h>

#define THREADS 4
#define ROUNDS 20000

static adamas_value head;

/* Обход детей звена - тот, что порождало бы понижение по типу (`release.c`). */
static void spine(adamas_value value) {
    adamas_share(adamas_field(value, 0), spine);
}

static void spine_release(adamas_value value) {
    adamas_drop(adamas_field(value, 0), spine_release);
}

static void *walk(void *arg) {
    (void)arg;
    adamas_value tail = adamas_field(head, 0);
    for (int round = 0; round < ROUNDS; round += 1) {
        adamas_dup(tail);
    }
    return NULL;
}

int main(void) {
    pthread_t threads[THREADS];
    unsigned taken;
    adamas_value tail = adamas_alloc(0, 1);
    adamas_set_field(tail, 0, adamas_imm(2));
    head = adamas_alloc(0, 1);
    adamas_set_field(head, 0, tail);
    MARK;
    for (int at = 0; at < THREADS; at += 1) {
        pthread_create(&threads[at], NULL, walk, NULL);
    }
    for (int at = 0; at < THREADS; at += 1) {
        pthread_join(threads[at], NULL);
    }
    taken = adamas_rc(tail);
    printf("tail rc=%u shared=%d\n", taken, adamas_is_shared(tail));
    /* Отдаётся ровно столько, сколько счётчик показал: иначе ломаный стенд,
     * потерявший инкрементации, уводил бы счётчик ниже нуля и падал. */
    for (unsigned at = 0; at < taken; at += 1) {
        adamas_drop(tail, NULL);
    }
    adamas_drop(head, spine_release);
    printf("live=%zu\n", adamas_stat_live_everywhere());
    return 0;
}
"#;

/// Граница §5.2: **запись в уже разделённый объект**.
///
/// Единственное место, где она достижима, - ячейка указательного массива. Поля
/// конструктора пишутся при постройке, когда объект ещё локален, а
/// `adamas_reuse` пометку снимает; ячейку же переписывают когда угодно.
///
/// Ход стенда - ровно тот, которым граница ломается:
///
/// 1. массив разделяется обходом: пометка встаёт на нём и на первом постояльце;
/// 2. второго владельца не остаётся - массив снова уникален;
/// 3. ячейка переписывается **локальным** значением;
/// 4. массив разделяется второй раз.
///
/// Без правки четвёртый шаг видит пометку на самом массиве, останавливается - и
/// до нового постояльца не доходит. Он и есть тот, чей счётчик потоки правят
/// голым `+=`.
///
/// Свидетеля у границы не было потому, что массив разделяемым не становился
/// нигде: круг был однопоточным. Здесь его разделяет `pthread_create` - то же,
/// что сделает `spawn` (§5.2).
const CELL: &str = r#"
#include "adamas.h"
#include <pthread.h>
#include <stdio.h>

#define THREADS 4
#define ROUNDS 20000

static adamas_value tenant;

/* Обход детей: массив спрашивает рантайм, звено - одно поле. */
static void children(adamas_value value) {
    if (adamas_tag(value) == ADAMAS_TAG_ARRAY) {
        adamas_array_promote(value, children);
        return;
    }
    adamas_share(adamas_field(value, 0), children);
}

static void children_release(adamas_value value) {
    if (adamas_tag(value) == ADAMAS_TAG_ARRAY) {
        adamas_array_release(value, children_release);
        return;
    }
    adamas_drop(adamas_field(value, 0), children_release);
}

static adamas_value link(intptr_t number) {
    adamas_value made = adamas_alloc(0, 1);
    adamas_set_field(made, 0, adamas_imm(number));
    return made;
}

static void *walk(void *arg) {
    (void)arg;
    for (int round = 0; round < ROUNDS; round += 1) {
        adamas_dup(tenant);
    }
    return NULL;
}

int main(void) {
    pthread_t threads[THREADS];
    unsigned taken;
    adamas_value array = adamas_array_alloc(1, 0);
    adamas_value writable;
    adamas_array_init(array, 0, link(1));

    /* 1-2: разделён, потом снова единственному владельцу. */
    adamas_share(array, children);

    /* 3: ячейка переписывается локальным постояльцем. */
    writable = adamas_array_writable(array, children_release);
    KEEP;
    tenant = link(2);
    adamas_array_put(writable, 0, tenant, children_release);

    /* 4: второй промоушен обязан дойти до нового постояльца. */
    adamas_share(writable, children);

    for (int at = 0; at < THREADS; at += 1) {
        pthread_create(&threads[at], NULL, walk, NULL);
    }
    for (int at = 0; at < THREADS; at += 1) {
        pthread_join(threads[at], NULL);
    }
    taken = adamas_rc(tenant);
    printf("tenant rc=%u shared=%d\n", taken, adamas_is_shared(tenant));
    for (unsigned at = 0; at < taken; at += 1) {
        adamas_drop(tenant, NULL);
    }
    adamas_drop(writable, children_release);
    printf("live=%zu\n", adamas_stat_live_everywhere());
    return 0;
}
"#;

/// Честная ячейка: запись снимает пометку, второй обход доходит до постояльца.
fn honest_cell() -> String {
    CELL.replace("KEEP;", "(void)0;")
}

/// Ломаная - **прежний рантайм** дословно: пометка переживает запись.
///
/// Мутант возвращает ровно то поведение, какое было до этого трека:
/// `adamas_array_writable` отдавала уникальный блок как есть, с пометкой.
/// Заголовок открыт в `adamas.h`, поэтому написать это можно в стенде, не
/// трогая рантайм.
fn broken_cell() -> String {
    CELL.replace(
        "KEEP;",
        "adamas_header_of(writable)->flags |= ADAMAS_FLAG_SHARED;",
    )
}

/// Честный стенд: счётчик трогает только рантайм, объект помечен разделяемым.
fn honest() -> String {
    HARNESS
        .replace("MARK;", "adamas_share(target, NULL);")
        .replace("TAKE;", "adamas_dup(target);")
        .replace("GIVE;", "adamas_drop(target, NULL);")
}

/// Честный вложенный: промоушен идёт обходом, значит доходит до хвоста.
fn honest_nested() -> String {
    NESTED.replace("MARK;", "adamas_share(head, spine);")
}

/// Ломаный вложенный - **прежний рантайм** дословно: помечен один объект.
///
/// Мутант здесь не выдуман, а взят из истории: до этой правки `adamas_share`
/// принимала одно значение и метила его одного, тогда как §5.2 обещает
/// транзитивно достижимое. `NULL` вместо обхода и есть та реализация.
fn broken_nested() -> String {
    NESTED.replace("MARK;", "adamas_share(head, NULL);")
}

/// Ломаный: тот же ряд операций голым счётчиком, мимо рантайма.
///
/// Это и есть «неатомарный RC» дословно - то, чем счётчик был до этого трека.
/// Пометки нет: она ничего бы не меняла, счётчик правится в обход.
fn broken() -> String {
    HARNESS
        .replace("MARK;", "(void)0;")
        .replace("TAKE;", "adamas_header_of(target)->rc += 1;")
        .replace("GIVE;", "adamas_header_of(target)->rc -= 1;")
}

/// Что сказал прогон под санитайзером.
struct Watched {
    /// Собрался ли стенд вовсе.
    built: bool,
    /// Назвал ли санитайзер гонку.
    raced: bool,
    /// Что стенд напечатал.
    printed: String,
}

/// Каталог под стенды. Свой у этого теста: прогоны идут параллельно.
fn scratch() -> PathBuf {
    let dir = Path::new(env!("OUT_DIR")).join("race");
    let _ = std::fs::create_dir_all(&dir);
    dir
}

/// Собирает стенд с санитайзером и гоняет его.
///
/// # Panics
///
/// Не записался стенд, не запустился компилятор либо собранный бинарь: это
/// сломанное окружение, а не наблюдение.
#[allow(
    clippy::expect_used,
    reason = "заготовка теста: отказ здесь означает сломанное окружение"
)]
fn watched(stem: &str, text: &str) -> Watched {
    let dir = scratch();
    let source = dir.join(format!("{stem}.c"));
    let binary = dir.join(stem);
    std::fs::write(&source, text).expect("стенд обязан записываться");

    // Рантайм пересобирается **санитайзером** вместе со стендом, а не берётся
    // готовым: TSan видит только то, что инструментировано, и счётчик, собранный
    // без него, оказался бы для него невидим. Ровно тот жанр обманчивого
    // свидетеля, от которого стенд и заводится.
    let sources = Path::new(env!("ADAMAS_RUNTIME_SOURCES"));
    let compiled = Command::new(env!("ADAMAS_CC"))
        .args(["-std=c11", "-O1", "-g", "-fsanitize=thread", "-pthread"])
        .arg("-I")
        .arg(env!("ADAMAS_RUNTIME_INCLUDE"))
        .arg(&source)
        .args(
            env!("ADAMAS_RUNTIME_UNITS")
                .split(',')
                .map(|unit| sources.join(unit)),
        )
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("компилятор обязан запускаться");
    if !compiled.status.success() {
        return Watched {
            built: false,
            raced: false,
            printed: String::from_utf8_lossy(&compiled.stderr).into_owned(),
        };
    }

    let ran = Command::new(&binary)
        .output()
        .expect("стенд обязан запускаться");
    let complained = String::from_utf8_lossy(&ran.stderr).into_owned();
    Watched {
        built: true,
        raced: complained.contains("data race"),
        printed: String::from_utf8_lossy(&ran.stdout).trim_end().to_owned(),
    }
}

/// Санитайзер молчит на рантайме и кричит на голом счётчике.
///
/// Обе половины обязательны. Без первой утверждение «атомарно» держалось бы на
/// том, что инструмент вообще не запустился; без второй - на том, что он ничего
/// не умеет ловить.
#[test]
fn the_sanitizer_names_the_race_the_runtime_does_not_have() {
    let broken = watched("broken", &broken());
    if !broken.built {
        // Не «пропустить молча»: сказать и остановиться. Отсутствие
        // санитайзера - факт окружения, и читать его должен человек.
        eprintln!(
            "ThreadSanitizer недоступен у `ADAMAS_CC`, договор §5.1 этим прогоном не проверялся:\n{}",
            broken.printed
        );
        return;
    }
    assert!(
        broken.raced,
        "санитайзер не назвал гонку там, где счётчик правится голым `+=`: \
         инструмент не ловит ничего, и молчание на честном стенде ничего не значит"
    );

    let honest = watched("honest", &honest());
    assert!(
        honest.built,
        "честный стенд не собрался:\n{}",
        honest.printed
    );
    assert!(
        !honest.raced,
        "санитайзер назвал гонку на счётчике рантайма: атомарности нет"
    );
    // Ряд взятий и отдач сбалансирован, значит объект обязан вернуться к
    // уникальности, а после последнего дропа - не остаться живым.
    assert_eq!(
        honest.printed, "rc=0 unique=1\nlive=0",
        "честный стенд посчитал не то"
    );
    eprintln!(
        "санитайзер: ломаный стенд - гонка, честный - тишина, {}",
        honest.printed.replace('\n', ", ")
    );
}

/// Промоушен одного объекта оставляет гонку на его ребёнке (§5.2).
///
/// Свидетель расхождения, которое до этого держалось **чтением**: §5.2 обещает
/// транзитивно достижимое, а рантайм метил один объект, и различить это было
/// нечем - настоящих потоков у питомника нет. Различает вот этот стенд, и
/// настоящих потоков ему не понадобилось: значение пересекает поток тем же
/// `pthread_create`, каким его пересекает соседний стенд атомарности, - это и
/// есть ровно то, что сделает `spawn`, когда круг станет многопоточным.
///
/// Обе половины обязательны, как и у соседа. Ломаная - **прежняя реализация**
/// дословно, и она обязана дать гонку; честная обязана молчать.
#[test]
fn the_sanitizer_names_the_race_on_a_child_of_a_shared_value() {
    let broken = watched("broken-nested", &broken_nested());
    if !broken.built {
        eprintln!(
            "ThreadSanitizer недоступен у `ADAMAS_CC`, договор §5.2 этим прогоном не проверялся:\n{}",
            broken.printed
        );
        return;
    }
    assert!(
        broken.raced,
        "санитайзер не назвал гонку на ребёнке, которого промоушен одного объекта не пометил: \
         инструмент не ловит ничего, и молчание на честном стенде ничего не значит"
    );

    let honest = watched("honest-nested", &honest_nested());
    assert!(
        honest.built,
        "честный стенд не собрался:\n{}",
        honest.printed
    );
    assert!(
        !honest.raced,
        "санитайзер назвал гонку на счётчике ребёнка: промоушен до него не дошёл"
    );
    // 4 потока по 20 000 взятий: ни одно не потеряно, пометка на хвосте стоит,
    // и после отданных ссылок блоков не остаётся.
    assert_eq!(
        honest.printed, "tail rc=80000 shared=1\nlive=0",
        "честный стенд посчитал не то"
    );
    eprintln!(
        "санитайзер: промоушен одного объекта - гонка на ребёнке, обход - тишина, {}",
        honest.printed.replace('\n', ", ")
    );
}

/// Запись в уже разделённый массив: граница §5.2 закрыта, и это различимо.
///
/// Свидетеля у неё не было вовсе - массив разделяемым не становился нигде, -
/// и держалась она **чтением**. Здесь её различает тот же инструмент и тем же
/// способом, что и транзитивность: значение пересекает поток
/// `pthread_create`'ом, ровно как его пересечёт `spawn`.
///
/// Ломаная половина - прежний рантайм дословно: пометка переживает запись.
#[test]
fn the_sanitizer_names_the_race_on_a_tenant_written_into_a_shared_array() {
    let broken = watched("broken-cell", &broken_cell());
    if !broken.built {
        eprintln!(
            "ThreadSanitizer недоступен у `ADAMAS_CC`, граница §5.2 этим прогоном не проверялась:\n{}",
            broken.printed
        );
        return;
    }
    assert!(
        broken.raced,
        "санитайзер не назвал гонку на постояльце, до которого второй обход не дошёл: \
         инструмент не ловит ничего, и молчание на честном стенде ничего не значит"
    );

    let honest = watched("honest-cell", &honest_cell());
    assert!(
        honest.built,
        "честный стенд не собрался:\n{}",
        honest.printed
    );
    assert!(
        !honest.raced,
        "санитайзер назвал гонку на постояльце разделённого массива: запись пометку не сняла"
    );
    assert_eq!(
        honest.printed, "tenant rc=80000 shared=1\nlive=0",
        "честный стенд посчитал не то"
    );
    eprintln!(
        "санитайзер: пометка, пережившая запись, - гонка на постояльце; снятая - тишина, {}",
        honest.printed.replace('\n', ", ")
    );
}
