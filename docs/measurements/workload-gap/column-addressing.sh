#!/usr/bin/env bash
# Чего стоит форма адресации ячейки на LLVM-пути, и чего стоят метаданные.
#
# Строка 4а второго столбца снята (трек B волны 3 Фазы 7), и число её - 0.877 в
# пользу LLVM-пути. Здесь мерится то, чего в ней **не** видно: сколько стоит
# то, что адрес ячейки считает рантайм (`adamas_array_at`), а не сам IR.
#
# Четыре варианта одного и того же `.ll`, различающиеся ровно формой обращения
# к ячейке; все четыре печатают один ответ и выдают один блок:
#
#   base    - как эмитит сегодня: `adamas_array_at` вызовом;
#   gepck   - адрес считает IR, шаг константой, проверка границы по месту;
#   gep     - он же **без** проверки границы: нижняя оценка, не кандидат;
#   gepin   - `gep` плюс `inbounds`: мера того, что даёт сам флаг.
#
# Метаданные алиасинга здесь **не мерятся временем**: на них ответ даёт счёт
# инструкций, и он ноль (`adamas-codegen/tests/alias.rs`,
# `alias_metadata_earns_nothing_on_memory_either`). Тот же тест несёт
# положительный контроль - счётчик двигается, но двигает его не метаданное.
#
# Артефакты берутся у стенда: он собирает `.ll` полной колонки, рантайм и
# спутник битовым кодом. Прогон стенда в режиме `--test` их и кладёт.
#
# Оценка - пол выборки, чередование сторон внутри блока. Привязка к ядру -
# параметром.
set -eu

CPU="${CPU:-8}"
BLOCKS="${BLOCKS:-5}"
RUNS="${RUNS:-5}"

root=$(cd "$(dirname "$0")/../../.." && pwd)
work="${TMPDIR:-/tmp}/adamas-column-addressing"
mkdir -p "$work"

echo "== стенд кладёт артефакты полной колонки"
cargo bench -q -p adamas-codegen --bench workloads -- --test column >/dev/null 2>&1

out=$(ls -d "$root"/target/release/build/adamas-codegen-*/out/bench-workloads 2>/dev/null | head -1)
if [ -z "$out" ] || [ ! -f "$out/column-llvm.ll" ]; then
    echo "артефактов стенда нет: ожидался $out/column-llvm.ll" >&2
    exit 1
fi
cp "$out/column-llvm.ll" "$work/base.ll"

# --- варианты --------------------------------------------------------------

# Адрес считает сам IR: шаг четыре байта (колонка `Float32`), граница по месту.
sed -e 's|^  %t\([0-9]*\) = call ptr @adamas_array_at(ptr \(%[A-Za-z0-9_]*\), i64 \(%[A-Za-z0-9_]*\))$|  %c\1.p = getelementptr i8, ptr \2, i64 8\n  %c\1.n = load i64, ptr %c\1.p\n  %c\1.ok = icmp ult i64 \3, %c\1.n\n  br i1 %c\1.ok, label %cell\1.in, label %cell\1.out\n\ncell\1.out:\n  call void @adamas_fail(ptr @.str.tag)\n  unreachable\n\ncell\1.in:\n  %c\1.off = mul i64 \3, 4\n  %c\1.pay = getelementptr i8, ptr \2, i64 24\n  %t\1 = getelementptr i8, ptr %c\1.pay, i64 %c\1.off|' \
    "$work/base.ll" > "$work/gepck.ll"

# Он же без проверки границы - нижняя оценка.
sed -e 's|^  %t\([0-9]*\) = call ptr @adamas_array_at(ptr \(%[A-Za-z0-9_]*\), i64 \(%[A-Za-z0-9_]*\))$|  %c\1.off = mul i64 \3, 4\n  %c\1.pay = getelementptr i8, ptr \2, i64 24\n  %t\1 = getelementptr i8, ptr %c\1.pay, i64 %c\1.off|' \
    "$work/base.ll" > "$work/gep.ll"

# И он же с `inbounds`.
sed -e 's/getelementptr i8/getelementptr inbounds i8/' "$work/gep.ll" > "$work/gepin.ll"

# --- сборка тем же конвейером, каким собирает стенд ------------------------

build() {
    local name="$1"
    llvm-as "$work/$name.ll" -o "$work/$name.bc"
    llvm-link "$work/$name.bc" "$out/runtime.bc" "$out/column-llvm.support.bc" \
        -o "$work/$name.linked.bc"
    opt -O2 "$work/$name.linked.bc" -o "$work/$name.opt.bc"
    llc -O2 -filetype=obj -relocation-model=pic "$work/$name.opt.bc" -o "$work/$name.o"
    "${ADAMAS_CC:-cc}" "$work/$name.o" -std=c11 -O2 -flto -o "$work/$name.bin"
}

echo
echo "== ответ, блоки и инструкции в горячей функции"
for name in base gepck gep gepin; do
    build "$name"
    answer=$("$work/$name.bin" 2>/dev/null)
    blocks=$("$work/$name.bin" 2>&1 >/dev/null)
    count=$(llvm-objdump -d --disassemble-symbols=adamas_entry "$work/$name.o" \
                | grep -c "$(printf '\t')" || true)
    printf '%-7s ответ %s, %s, инструкций %s\n' "$name" "$answer" "$blocks" "$count"
done

# --- отношение чередованием ------------------------------------------------

floor() {
    local best=999999999 t0 t1 d
    for _ in $(seq 1 "$RUNS"); do
        t0=$(date +%s%N); "$1" >/dev/null 2>&1; t1=$(date +%s%N)
        d=$(((t1 - t0) / 1000))
        [ "$d" -lt "$best" ] && best=$d
    done
    echo "$best"
}

race() {
    local left="$1" right="$2"
    echo
    echo "== $left против $right, чередованием"
    for block in $(seq 1 "$BLOCKS"); do
        a=$(floor "$work/$left.bin")
        b=$(floor "$work/$right.bin")
        awk -v a="$a" -v b="$b" -v n="$block" \
            'BEGIN { printf "блок %d: %.3f против %.3f мс, отношение %.4f\n", n, a/1000, b/1000, a/b }'
    done
}

if [ "${CPU}" = "-" ]; then
    race base gepck
    race base gep
else
    taskset -c "$CPU" bash -c "$(declare -f floor race); work=$work; BLOCKS=$BLOCKS; RUNS=$RUNS; race base gepck; race base gep"
fi
