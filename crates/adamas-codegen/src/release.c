/* Дроп детей: то, что `adamas_drop` зовёт на последней ссылке.
 *
 * `adamas.h` требует, чтобы release порождало понижение: рантайм полиморфным
 * быть не может - какие у объекта дети, знает тип, а числа полей в заголовке
 * нет. Здесь он один на программу и читает **таблицу по тегу** - ту же, по
 * которой печатается ответ, и по тому же доводу: тип известен вершине, а ниже
 * идут значения, чьих типов ответ не называет. Порождать release по всему
 * достижимому графу типов пришлось бы ради того же одного чтения тега.
 *
 * Плоский слот дроп **пропускает**, и это не оптимизация: у плоского значения
 * заголовка нет вовсе (§4.11), в слоте лежат биты числа, и отдать их
 * `adamas_drop` значило бы уменьшить счётчик по адресу этого числа. Какой слот
 * плоский, говорит `adamas_slot_kind` - та же таблица, по которой печатает
 * ответ.
 *
 * Замыкание разбирается отдельной веткой: его слоты - среда плюс накопленные
 * аргументы, и сколько их занято, знает рантайм (`applied` меняется от
 * частичного применения, а указатель на release остаётся тот же).
 */

static void adamas_release_value(adamas_value value);

/* Дроп значения программы. Одна точка на все места дропа - иначе имя release'а
 * пришлось бы писать в каждом. */
static void adamas_drop_value(adamas_value value) {
    adamas_drop(value, adamas_release_value);
}

/* Он же, придерживающий блок под переписывание (§5.1). */
static adamas_value adamas_reclaim_value(adamas_value value) {
    return adamas_drop_reuse(value, adamas_release_value);
}

static void adamas_release_value(adamas_value value) {
    uint16_t tag = adamas_tag(value);
    size_t index;
    size_t fields;
    if (tag == ADAMAS_TAG_CLOSURE) {
        fields = adamas_closure_taken(value);
        for (index = 0; index < fields; index += 1) {
            adamas_drop_value(adamas_closure_get(value, index));
        }
        return;
    }
    if (tag == ADAMAS_TAG_ARRAY) {
        /* Массив - один объект на всю длину (§5.1): дропает его рантайм, потому
         * что длину знает он. У плоского дропать нечего вовсе - заголовков у
         * ячеек нет. */
        adamas_array_release(value, adamas_release_value);
        return;
    }
    if ((size_t)tag >= ADAMAS_CONSTRUCTORS) {
        /* Чужой тег: служебные объекты рантайма дропает он сам, а стёртая
         * позиция непосредственна и сюда не доходит вовсе. */
        return;
    }
    fields = adamas_con_slots[tag];
    for (index = 0; index < fields; index += 1) {
        if (adamas_slot_kind[adamas_con_slot0[tag] + index] != ADAMAS_FLAT_BOXED) {
            continue;
        }
        adamas_drop_value(adamas_field(value, index));
    }
}
