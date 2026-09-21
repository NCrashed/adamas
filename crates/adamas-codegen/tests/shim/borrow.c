/* Счётчик одолженного массива, пока внутри чужого вызова бежит **наш** код
 * (§10 вопрос 184, §5.3 уровень 2).
 *
 * Спутник `ownership.c` читает тот же заголовок, но отвечает на другой вопрос:
 * там счётчик спрашивается до и после вызова, здесь - **в середине**, пока
 * управление у Adamas-колбэка. Разница и есть предмет вопроса 184: до волны
 * колбэков между входом в чужой вызов и возвратом из него ничего нашего не
 * бежало, и `rc == 0` держался обстоятельством.
 *
 * Знание о нашем заголовке то же и той же ширины: нагрузка массива идёт со
 * смещения 24, счётчик - первое слово, тег - следующие два байта. Оба числа
 * закреплены `_Static_assert`'ами в `adamas.h`.
 */

#include <stdint.h>

/* Смещение нагрузки плоского массива: `sizeof(adamas_array)`. */
#define PAYLOAD 24u

/* Тег массива: `ADAMAS_TAG_ARRAY`. */
#define TAG_ARRAY 0xFFFBu

static const unsigned char *header_of(const unsigned char *payload) {
    return payload - PAYLOAD;
}

static uint32_t counter(const unsigned char *bytes) {
    uint32_t rc;
    __builtin_memcpy(&rc, header_of(bytes), sizeof rc);
    return rc;
}

static uint16_t tag_of(const unsigned char *bytes) {
    uint16_t tag;
    __builtin_memcpy(&tag, header_of(bytes) + 4, sizeof tag);
    return tag;
}

/* Одолженный массив, наш колбэк и его `userdata`.
 *
 * Колбэк зовётся **один раз** и получает адрес нагрузки обоими ключами: что за
 * этими словами стоит, трамплин не различает, а свидетелю важно лишь то, что
 * наш код побежал внутри чужого кадра.
 *
 * Ответ трёхзначный: сотни - счётчик, прочитанный **пока колбэк ещё не
 * позван**, десятки - он же **после** возврата из колбэка, единицы - сверка
 * тега. Счётчик у массива, одолженного владением, есть ноль, то есть
 * `adamas_is_unique` о нём говорит «владелец один», - и говорит это в тот
 * самый момент, когда бежит наш код.
 */
uint64_t adamas_probe_during(const unsigned char *bytes,
                             int32_t (*callback)(uint64_t, uint64_t, void *), void *userdata) {
    uint64_t before = counter(bytes);
    (void)callback((uint64_t)(uintptr_t)bytes, (uint64_t)(uintptr_t)bytes, userdata);
    uint64_t after = counter(bytes);
    uint64_t sound = tag_of(bytes) == TAG_ARRAY ? 1u : 0u;
    return before * 100u + after * 10u + sound;
}
