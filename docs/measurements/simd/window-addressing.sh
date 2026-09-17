#!/usr/bin/env bash
# Чего стоит форма адресации **окна** и чего стоит обещание границы (§4.9).
#
# Родня `docs/measurements/workload-gap/column-addressing.sh`, и вопросы те же
# два, только над векторным ядром строки 4б, а не над скалярным ядром 4а.
#
# Первый вопрос - **адрес**. Трек B волны 3 намерил на скалярной колонке, что
# адрес ячейки, посчитанный самим IR константным шагом вместо вызова рантайма,
# даёт 1.230 раза, и оставил развилку следующему треку. У вектора обращений к
# рантайму на виток вдвое меньше, а работы на обращение - вдесятеро больше,
# поэтому цена вызова обязана быть **другой**, и какой именно - здесь и
# меряется.
#
# Второй вопрос - **граница**. Эмиттер пишет `align 4`: ячейка `Float32` стоит
# по шагу колонки, и больше ей никто ничего не обещал. Нагрузка массива лежит
# по смещению 24 от блока (`adamas.h`), то есть выровнена она **по восьми** и
# ни по чему больше - `AlignedBuffer` §4.9 при такой раскладке невыразим в
# принципе. Меряется поэтому то, что измеримо: даёт ли что-нибудь обещание
# сверх правды.
#
# Варианты одного и того же `.ll`, различающиеся ровно одной вещью:
#
#   base    - как эмитит сегодня: `adamas_array_window` вызовом, `align 4`;
#   gepck   - адрес считает IR, шаг константой, проверка хвоста по месту;
#   gep     - он же **без** проверки: нижняя оценка, не кандидат;
#   align8  - `base`, но обещано восемь: ровно то, что нагрузка и гарантирует;
#   align32 - `base`, но обещано тридцать два: **ложь** при этой раскладке, и
#             взята она нарочно - если и максимальная ложь в пользу выравнивания
#             не двигает ни инструкций, ни времени, покупать `AlignedBuffer`
#             нечего. Прогон её поэтому может и оборваться; это тоже ответ.
#
# Артефакты берёт у стенда, как и скалярный близнец.
set -eu

CPU="${CPU:-8}"
BLOCKS="${BLOCKS:-5}"
RUNS="${RUNS:-5}"

root=$(cd "$(dirname "$0")/../../.." && pwd)
work="${TMPDIR:-/tmp}/adamas-window-addressing"
mkdir -p "$work"

echo "== стенд кладёт артефакты векторной колонки"
cargo bench -q -p adamas-codegen --bench workloads -- --test vector >/dev/null 2>&1

out=$(ls -d "$root"/target/release/build/adamas-codegen-*/out/bench-workloads 2>/dev/null | head -1)
if [ -z "$out" ] || [ ! -f "$out/vector-llvm.ll" ]; then
    echo "артефактов стенда нет: ожидался $out/vector-llvm.ll" >&2
    exit 1
fi
cp "$out/vector-llvm.ll" "$work/base.ll"

# Имя строки обрыва берётся у самого модуля: их там может быть несколько, и
# прибитое гвоздями имя молча не нашлось бы. Текст у неё чужой - первая
# попавшаяся строка модуля, - и это законно ровно потому, что на штатной
# колонке проверка не срабатывает ни разу: мерится цена адреса, а не текст
# обрыва. Настоящему эмиттеру пришлось бы звать свою точку входа рантайма,
# чтобы сообщение осталось в одном экземпляре.
tag=$(grep -o '@\.str\.[a-z]*' "$work/base.ll" | head -1)
if [ -z "$tag" ]; then
    echo "в модуле нет ни одной строки обрыва: мутанту нечем звать adamas_fail" >&2
    exit 1
fi

# --- варианты --------------------------------------------------------------

# Адрес считает сам IR. Шаг четыре байта (колонка `Float32`), нагрузка с 24,
# длина по смещению 8 - те же три числа, что у скалярного близнеца, плюс
# проверка **хвоста**: `lanes <= count` и `at <= count - lanes`.
sed -e "s|^  %t\([0-9]*\) = call ptr @adamas_array_window(ptr \(%[A-Za-z0-9_]*\), i64 \(%[A-Za-z0-9_]*\), i64 \([0-9]*\))\$|  %c\1.p = getelementptr i8, ptr \2, i64 8\n  %c\1.n = load i64, ptr %c\1.p\n  %c\1.wide = icmp uge i64 %c\1.n, \4\n  br i1 %c\1.wide, label %win\1.fits, label %win\1.out\n\nwin\1.fits:\n  %c\1.lim = sub i64 %c\1.n, \4\n  %c\1.ok = icmp ule i64 \3, %c\1.lim\n  br i1 %c\1.ok, label %win\1.in, label %win\1.out\n\nwin\1.out:\n  call void @adamas_fail(ptr $tag)\n  unreachable\n\nwin\1.in:\n  %c\1.off = mul i64 \3, 4\n  %c\1.pay = getelementptr i8, ptr \2, i64 24\n  %t\1 = getelementptr i8, ptr %c\1.pay, i64 %c\1.off|" \
    "$work/base.ll" > "$work/gepck.ll"

# Он же без проверки - нижняя оценка.
sed -e "s|^  %t\([0-9]*\) = call ptr @adamas_array_window(ptr \(%[A-Za-z0-9_]*\), i64 \(%[A-Za-z0-9_]*\), i64 \([0-9]*\))\$|  %c\1.off = mul i64 \3, 4\n  %c\1.pay = getelementptr i8, ptr \2, i64 24\n  %t\1 = getelementptr i8, ptr %c\1.pay, i64 %c\1.off|" \
    "$work/base.ll" > "$work/gep.ll"

# Обещание границы - только оно, адрес как был.
sed -e 's|\(<8 x float>.*ptr %t[0-9]*\), align 4|\1, align 8|' "$work/base.ll" > "$work/align8.ll"
sed -e 's|\(<8 x float>.*ptr %t[0-9]*\), align 4|\1, align 32|' "$work/base.ll" > "$work/align32.ll"

# --- сборка тем же конвейером, каким собирает стенд ------------------------

build() {
    local name="$1"
    llvm-as "$work/$name.ll" -o "$work/$name.bc"
    llvm-link "$work/$name.bc" "$out/runtime.bc" "$out/vector-llvm.support.bc" \
        -o "$work/$name.linked.bc"
    opt -O2 "$work/$name.linked.bc" -o "$work/$name.opt.bc"
    llc -O2 -filetype=obj -relocation-model=pic "$work/$name.opt.bc" -o "$work/$name.o"
    "${ADAMAS_CC:-cc}" "$work/$name.o" -std=c11 -O2 -flto -o "$work/$name.bin"
}

echo
echo "== ответ, блоки и инструкции в горячей функции"
for name in base gepck gep align8 align32; do
    build "$name"
    answer=$("$work/$name.bin" 2>/dev/null || echo "ОБРЫВ")
    blocks=$("$work/$name.bin" 2>&1 >/dev/null || true)
    count=$(llvm-objdump -d --disassemble-symbols=adamas_entry "$work/$name.o" \
                | grep -c "$(printf '\t')" || true)
    moves=$(llvm-objdump -d --disassemble-symbols=adamas_entry "$work/$name.o" \
                | grep -cE 'movups|movaps' || true)
    printf '%-8s ответ %s, %s, инструкций %s, пакетных перемещений %s\n' \
        "$name" "$answer" "$blocks" "$count" "$moves"
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
    race base align8
    race base align32
else
    taskset -c "$CPU" bash -c "$(declare -f floor race); work=$work; BLOCKS=$BLOCKS; RUNS=$RUNS; race base gepck; race base gep; race base align8; race base align32"
fi
