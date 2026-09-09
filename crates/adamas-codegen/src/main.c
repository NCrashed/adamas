/* Точка входа: печать ответа и счётчики блоков.
 *
 * Форм у ответа две, и различает их представление (§4.11). Боксированный
 * приходит владением, как всё в этом понижении, и дропается здесь же. Плоский
 * лежит в регистре: заголовка у него нет, счётчика нет, отдавать нечего -
 * печатается он по сорту, который назвало понижение.
 */

static void adamas_answer(void) {
#ifdef ADAMAS_ANSWER_FLAT
    ADAMAS_ANSWER_TYPE answer = ADAMAS_ENTRY();
    adamas_print_flat(ADAMAS_ANSWER_KIND, ADAMAS_ANSWER_FLAT(answer), 0);
    printf("\n");
#else
    adamas_value answer = ADAMAS_ENTRY();
    adamas_print(answer, 0);
    printf("\n");
    /* Не отдай его здесь - живым остался бы ровно он, и счётчик показал бы это
     * числом. */
    adamas_drop_value(answer);
#endif
}

int main(void) {
    adamas_answer();
    /* Выдано против живого. Второе - критерий «течи нет»; первое - свидетель
     * reuse и плоского значения разом: переписанная ячейка выдачей не
     * считается, а под арифметику ячейка не выдаётся вовсе. */
    fprintf(stderr, "блоков выдано %zu, живо %zu\n", adamas_stat_allocated(),
            adamas_stat_live());
    return 0;
}
