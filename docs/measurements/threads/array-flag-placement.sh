#!/usr/bin/env bash
# Куда ставить снятие пометки разделяемости у массива (§5.2, трек E волны 3).
#
# Граница «запись в уже разделённый объект обходом второй раз не покрывается»
# закрывается тем, что уникальный массив перестаёт считаться разделённым. Место
# у этой правки выбрано замером, и вот он.
#
# Три рантайма, одна программа - колонное ядро, строка 4а таблицы разрыва:
#
#   none      правки нет вовсе - опорная точка;
#   put       правка в `adamas_array_put`      - так сделано;
#   writable  правка в `adamas_array_writable` - так было сделано сначала.
#
# Плоский массив до `adamas_array_put` не доходит (пишет он через
# `adamas_array_at`), поэтому `put` обязан совпасть с `none`, а `writable` -
# разойтись. Разошёлся он в 1.497 раза, и это тот же жанр, что нашёл трек B:
# лишний код в точке входа переворачивает решение инлайнера.
#
# Оценка - пол выборки, стороны чередуются в одном окне: тихой машины нет.
set -eu

ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
CORE="${CORE:-8}"
ROUNDS="${ROUNDS:-9}"

# Программа берётся та, которую собрал стенд таблицы разрыва: 8388608 ячеек в
# восемь проходов. Нет её - сказать об этом, а не мерить корпусный размер, на
# котором виток идёт три миллисекунды и не меряет ничего.
PROG="${PROG:-$(ls "$ROOT"/target/*/build/adamas-codegen-*/out/bench-workloads/column.c 2>/dev/null | head -1)}"
if [ -z "$PROG" ]; then
    echo "нет порождённого column.c: сперва 'cargo bench -p adamas-codegen --bench workloads'" >&2
    exit 1
fi

DIR="$(mktemp -d)"
trap 'rm -rf "$DIR"' EXIT

# Правка в `adamas_array_put`, как она стоит в дереве.
IN_PUT='    if (adamas_header_of(array)->flags != 0) {
        localised(array);
    }
'
# Она же, перенесённая в `adamas_array_writable`.
BARE='    if (adamas_is_unique(array)) {
        return array;
    }'
IN_WRITABLE='    if (adamas_is_unique(array)) {
        adamas_header *head = adamas_header_of(array);
        if (head->flags != 0) {
            head->flags = 0;
        }
        return array;
    }'

# Замена дословной подстроки: `perl` в режиме слурпа, обе стороны через
# окружение - в шаблон они не попадают, значит и экранировать нечего.
swap() {
    ADAMAS_FROM="$2" ADAMAS_TO="$3" perl -0pi -e '
        my ($from, $to) = ($ENV{ADAMAS_FROM}, $ENV{ADAMAS_TO});
        my $at = index($_, $from);
        die "подстрока не нашлась\n" if $at < 0;
        substr($_, $at, length($from)) = $to;
    ' "$1"
}

for side in none put writable; do
    cp -r "$ROOT/crates/adamas-runtime/c" "$DIR/$side"
    case "$side" in
        put) ;;  # как в дереве
        none) swap "$DIR/$side/array.c" "$IN_PUT" "" ;;
        writable)
            swap "$DIR/$side/array.c" "$IN_PUT" ""
            swap "$DIR/$side/array.c" "$BARE" "$IN_WRITABLE"
            ;;
    esac
    gcc -std=c11 -O2 -flto -fwrapv -ffp-contract=off -w \
        -I "$ROOT/crates/adamas-runtime/include" "$PROG" "$DIR/$side"/*.c \
        -o "$DIR/$side.bin"
done

declare -A floor=([none]=999999999 [put]=999999999 [writable]=999999999)
for _ in $(seq "$ROUNDS"); do
    for side in none put writable; do
        start=$(date +%s%N)
        taskset -c "$CORE" "$DIR/$side.bin" >/dev/null 2>&1
        end=$(date +%s%N)
        took=$(( (end - start) / 1000 ))
        [ "$took" -lt "${floor[$side]}" ] && floor[$side]=$took
    done
done

printf 'пол: без правки %s мкс, в put %s, в writable %s\n' \
    "${floor[none]}" "${floor[put]}" "${floor[writable]}"
awk -v n="${floor[none]}" -v p="${floor[put]}" -v w="${floor[writable]}" 'BEGIN{
    printf "put/без = %.4f, writable/без = %.4f\n", p/n, w/n
}'
