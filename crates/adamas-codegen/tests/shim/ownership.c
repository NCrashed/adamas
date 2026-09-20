/* Свидетель владения одолженным буфером (§5.3, §5.1, §10 вопрос 149).
 *
 * Эта единица про Adamas знает **нарочно**: она читает заголовок нашего блока
 * по одолженному адресу. Иначе счётчик ссылок с той стороны границы не увидеть
 * вовсе - а увидеть его и есть весь предмет. Спутник свидетеля границы
 * (`buffer.c`) устроен обратным образом и не знает ничего; смешивать их нельзя,
 * потому что тогда первый перестал бы отвечать на свой вопрос.
 *
 * Знание ограничено двумя числами, и оба закреплены `_Static_assert`'ами в
 * `adamas.h`: нагрузка массива идёт со смещения 24, заголовок занимает первое
 * слово и начинается счётчиком (`rc (32) | tag (16) | flags (16)`). Разъедься
 * они - свидетель соврёт, поэтому второй его половиной стоит сверка тега.
 */

#include <stdint.h>

/* Смещение нагрузки плоского массива: `sizeof(adamas_array)`. */
#define PAYLOAD 24u

/* Тег массива: `ADAMAS_TAG_ARRAY`. Читается ради сверки, что смещение верно. */
#define TAG_ARRAY 0xFFFBu

/* Флаг разделяемости: `ADAMAS_FLAG_SHARED`. */
#define FLAG_SHARED 0x0001u

static const unsigned char *header_of(const unsigned char *payload) {
    return payload - PAYLOAD;
}

/* Счётчик ссылок блока, чья нагрузка одолжена.
 *
 * `rc == 0` значит «владелец один» (§5.1), а не «ссылок нет». */
uint64_t adamas_probe_counter(const unsigned char *bytes) {
    uint32_t rc;
    __builtin_memcpy(&rc, header_of(bytes), sizeof rc);
    return rc;
}

/* Тег блока: сверка того, что одолженный адрес и правда указывает в нагрузку
 * массива, а не куда-нибудь ещё. Без неё счётчик читался бы из произвольного
 * места и врал бы правдоподобным числом. */
uint64_t adamas_probe_tag(const unsigned char *bytes) {
    uint16_t tag;
    __builtin_memcpy(&tag, header_of(bytes) + 4, sizeof tag);
    return tag == TAG_ARRAY ? 1u : 0u;
}

/* Адрес, который чужая сторона **удержала** дольше вызова.
 *
 * Держать его язык не мешает ничем: это обычная статическая переменная чужой
 * библиотеки, и знать о ней нам нечем. Пара ниже и есть свидетель тому, что
 * обещания «указатель живёт ровно вызов» у уровня 1 нет: удержанный адрес
 * сверяется с адресом **другого** массива, заведённого после того, как первый
 * отдан. Разыменования тут нет - только сравнение, - потому что читать по
 * освобождённому адресу нельзя и в свидетеле.
 */
static uintptr_t kept = 0;

uint64_t adamas_probe_keep(const unsigned char *bytes) {
    kept = (uintptr_t)bytes;
    return 1u;
}

uint64_t adamas_probe_revisits(const unsigned char *bytes) {
    return (uintptr_t)bytes == kept ? 1u : 0u;
}

/* Помечен ли блок разделяемым (§5.2). */
uint64_t adamas_probe_shared(const unsigned char *bytes) {
    uint16_t flags;
    __builtin_memcpy(&flags, header_of(bytes) + 6, sizeof flags);
    return (flags & FLAG_SHARED) != 0u ? 1u : 0u;
}
