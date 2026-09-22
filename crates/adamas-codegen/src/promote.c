/* Промоушен детей: то, что `adamas_share` зовёт на не разделённом ещё объекте.
 *
 * Близнец `release.c` и построен так же, потому что задача та же: рантайм
 * полиморфным быть не может - какие у объекта дети, знает тип, а числа полей в
 * заголовке нет. Читается та же **таблица по тегу**, по которой идут дроп и
 * печать; второй таблицы не заводится.
 *
 * Плоский слот промоушен пропускает по той же причине, по которой его
 * пропускает дроп: у плоского значения заголовка нет вовсе (§4.11), в слоте
 * лежат биты числа, и поставить на них пометку значило бы записать флаг по
 * адресу этого числа.
 *
 * Печатается это только в программу с питомником: без `withNursery` значение
 * никуда не уезжает, и функция осталась бы неиспользованной.
 */

static void adamas_promote_value(adamas_value value);

/* Промоушен значения программы. Одна точка на все места, как у дропа. */
static void adamas_share_value(adamas_value value) {
    adamas_share(value, adamas_promote_value);
}

static void adamas_promote_value(adamas_value value) {
    uint16_t tag = adamas_tag(value);
    size_t index;
    size_t fields;
    if (tag == ADAMAS_TAG_CLOSURE) {
        /* Замыкание - главный постоялец этого пути: тело `spawn` есть оно, и
         * захват его и есть то, что уезжает в чужой поток (§5.2). Плоский слот
         * среды метить нечем - счётчика у битов числа нет, - и какой слот
         * счётный, говорит рантайм (`adamas_closure_slot_counted`). */
        fields = adamas_closure_taken(value);
        for (index = 0; index < fields; index += 1) {
            if (!adamas_closure_slot_counted(value, index)) {
                continue;
            }
            adamas_share_value(adamas_closure_get(value, index));
        }
        return;
    }
    if (tag == ADAMAS_TAG_SEGMENT) {
        /* Захваченная резумпция: обход её кадров держит рантайм, обход данных -
         * вот этот же указатель. */
        adamas_segment_promote(value, adamas_promote_value);
        return;
    }
    if (tag == ADAMAS_TAG_FIBER) {
        /* Невыразимое имя файбера: детей у него нет, а круг оно держит
         * несчётным полем - метить нечего. */
        return;
    }
    if (tag == ADAMAS_TAG_ARRAY) {
        adamas_array_promote(value, adamas_promote_value);
        return;
    }
    if ((size_t)tag >= ADAMAS_CONSTRUCTORS) {
        /* Чужой тег: служебные объекты рантайма он метит сам, а стёртая позиция
         * непосредственна и сюда не доходит вовсе. */
        return;
    }
    fields = adamas_con_slots[tag];
    for (index = 0; index < fields; index += 1) {
        if (adamas_slot_kind[adamas_con_slot0[tag] + index] != ADAMAS_FLAT_BOXED) {
            continue;
        }
        adamas_share_value(adamas_field(value, index));
    }
}
