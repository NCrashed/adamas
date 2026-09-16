#!/usr/bin/env bash
# Чего стоит холодная половина `writable` в области (§3.6).
#
# Аллокация в регионе есть точка входа с редкой тяжёлой ветвью: быстрый путь -
# поднять курсор и скопировать нагрузку, редкий - скопировать **всю** область,
# когда она разделена. Правило, заведённое треком B волны 3 Фазы 7, говорит, что
# такую точку обязан делить исходник, а не компилятор: у gcc частичный инлайнинг
# делит её сам, а `PartialInlinerPass` в `-O2` конвейера LLVM выключен по
# умолчанию.
#
# Здесь это проверяется на самой области. Две точки, различающиеся **одним
# атрибутом** у `copied` в `region.c`:
#
#   plain - `static adamas_value copied(...)`: делит компилятор;
#   split - `__attribute__((noinline, cold)) static ...`: делит исходник.
#
# Третьей точки - «половины слиты обратно в одну функцию» - в стенде нет
# нарочно: она измерена отдельно и дала то же, что `plain` (1.01, 1.09, 0.98 к
# нему), потому что компилятор всё равно втягивает `copied` в `writable`. То
# есть **написать две функции - не значит разделить**; делит атрибут.
#
# Виток стенда - `regionAlloc` плюс `regionPop` над своей областью: область
# уникальна всякий виток, холодная половина не случается ни разу, и мерится
# ровно то, мешает ли она горячей. Ответ у обеих точек один (`8 1001`).
#
# Оценка - пол выборки, чередование сторон внутри блока, привязка к ядру.
set -eu

CPU="${CPU:-8}"
BLOCKS="${BLOCKS:-5}"
RUNS="${RUNS:-5}"
TURNS="${TURNS:-10000000}"

root=$(cd "$(dirname "$0")/../../.." && pwd)
include="$root/crates/adamas-runtime/include"
work="${TMPDIR:-/tmp}/adamas-region-alloc"
rm -rf "$work"
mkdir -p "$work/plain" "$work/split"

cp "$root"/crates/adamas-runtime/c/*.c "$work/split/"
cp "$root"/crates/adamas-runtime/c/*.c "$work/plain/"
sed -i 's/__attribute__((noinline, cold)) static adamas_value copied/static adamas_value copied/' \
    "$work/plain/region.c"
if cmp -s "$work/plain/region.c" "$work/split/region.c"; then
    echo "точки не разошлись: атрибута у `copied` в region.c нет вовсе" >&2
    exit 1
fi

cat > "$work/drive.c" <<'PROBE'
/* Виток аллокации в области: положить и опустить курсор (§3.6). */
#include "adamas.h"

#include <stdio.h>
#include <stdlib.h>

static void release(adamas_value value) { (void)value; }

int main(int argc, char **argv) {
    size_t turns = argc > 1 ? (size_t)atol(argv[1]) : 0;
    uint64_t seed = 1;
    adamas_value region = adamas_region_new();
    size_t turn;
    for (turn = 0; turn < turns; turn += 1) {
        region = adamas_region_alloc(region, &seed, sizeof(seed), sizeof(seed));
        seed += 1;
        region = adamas_region_pop(region, 0);
    }
    region = adamas_region_alloc(region, &seed, sizeof(seed), sizeof(seed));
    printf("%llu %llu\n", (unsigned long long)adamas_region_used(region),
           (unsigned long long)seed);
    adamas_drop(region, release);
    return 0;
}
PROBE

# --- сборка обеими цепочками ------------------------------------------------

for point in plain split; do
    "${ADAMAS_CC:-cc}" -std=c11 -O2 -flto -fwrapv -fno-strict-aliasing \
        -ffp-contract=off -I "$include" "$work/$point"/*.c "$work/drive.c" \
        -o "$work/$point.gcc.bin"

    units=()
    for source in "$work/$point"/*.c "$work/drive.c"; do
        unit="$work/$point.$(basename "$source" .c).bc"
        "${ADAMAS_CLANG:-clang}" -std=c11 -O1 -Xclang -disable-llvm-passes \
            -emit-llvm -c -I "$include" "$source" -o "$unit"
        units+=("$unit")
    done
    "${ADAMAS_LLVM_BIN:+$ADAMAS_LLVM_BIN/}llvm-link" "${units[@]}" -o "$work/$point.bc"
    "${ADAMAS_LLVM_BIN:+$ADAMAS_LLVM_BIN/}opt" -O2 "$work/$point.bc" -o "$work/$point.opt.bc"
    "${ADAMAS_LLVM_BIN:+$ADAMAS_LLVM_BIN/}llc" -O2 -filetype=obj -relocation-model=pic \
        "$work/$point.opt.bc" -o "$work/$point.llvm.o"
    "${ADAMAS_CC:-cc}" "$work/$point.llvm.o" -o "$work/$point.llvm.bin"
done

echo "== ответ и что осталось от половин в символах"
for point in plain split; do
    for chain in gcc llvm; do
        answer=$("$work/$point.$chain.bin" 1000)
        symbols=$(nm "$work/$point.$chain.bin" 2>/dev/null \
                      | grep -iE ' (t|T) (copied|writable)' \
                      | awk '{ print $3 }' | sort | tr '\n' ' ')
        printf '%-6s %-4s ответ «%s», символы: %s\n' \
            "$point" "$chain" "$answer" "${symbols:-нет}"
    done
done

# --- отношение чередованием -------------------------------------------------

floor() {
    local best=999999999 t0 t1 d
    for _ in $(seq 1 "$RUNS"); do
        t0=$(date +%s%N); "$1" "$TURNS" >/dev/null 2>&1; t1=$(date +%s%N)
        d=$(((t1 - t0) / 1000))
        [ "$d" -lt "$best" ] && best=$d
    done
    echo "$best"
}

race() {
    echo
    echo "== $1: plain против split, чередованием"
    for block in $(seq 1 "$BLOCKS"); do
        a=$(floor "$work/plain.$1.bin")
        b=$(floor "$work/split.$1.bin")
        awk -v a="$a" -v b="$b" -v n="$block" \
            'BEGIN { printf "блок %d: %.3f против %.3f мс, отношение %.4f\n", n, a/1000, b/1000, a/b }'
    done
}

if [ "$CPU" = "-" ]; then
    race gcc
    race llvm
else
    taskset -c "$CPU" bash -c \
        "$(declare -f floor race); work=$work; TURNS=$TURNS; RUNS=$RUNS; BLOCKS=$BLOCKS; race gcc; race llvm"
fi
