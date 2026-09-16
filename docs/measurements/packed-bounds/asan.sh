#!/usr/bin/env bash
# Читает ли `load iN` из плотного агрегата ровно N/8 байт (§4.11).
#
# Вопрос не праздный: LLVM-эмиттер держит плотный агрегат целым своей ширины,
# и `Vec3` из трёх `Float32` уезжает в ячейку колонки как `i96`. Ячейки такой
# колонки стоят по адресам 0, 12, 24, а блок кончается сразу за последней;
# прочитай `load i96` шестнадцать байт вместо двенадцати - и последняя ячейка
# читалась бы за концом блока. Ответ бы при этом не изменился: лишние четыре
# байта в ответ не входят.
#
# Меряется это ASan'ом поверх порождённого `.ll`. **Свидетель обязан
# различать**, и первая его редакция не различала: ASan правит только функции
# с атрибутом `sanitize_address`, порождённый `.ll` его не несёт, и без строки
# `sed` ниже инструментация не вставала вовсе - контроль с чтением в 64 КиБ за
# блоком проходил молча. Отсюда две проверки в стенде: число инструментированных
# мест печатается, а `--control` подменяет `load i96` на `load i128` и обязан
# уронить прогон.
set -eu

root=$(cd "$(dirname "$0")/../../.." && pwd)
include="$root/crates/adamas-runtime/include"
work="${TMPDIR:-/tmp}/adamas-packed-bounds"

# Фикстуры, у которых плотный агрегат либо область доходят до памяти рантайма.
NAMES=(array-aggregate array-nested array-tagged array-parametric soa-record
       flat flat-primitives flat-sealed-member region-holds-flat-payload
       region-strategies region-strategy-handled region-strategy-in-io
       functor-strategy workload-column)

echo '== стенд кладёт `.ll` корпуса'
cargo test -q -p adamas-codegen --test llvm the_corpus_agrees >/dev/null 2>&1 || true
out=$(ls -d "$root"/target/debug/build/adamas-codegen-*/out/llvm 2>/dev/null | head -1)
if [ -z "$out" ] || [ ! -f "$out/array-aggregate.llvm.ll" ]; then
    echo "артефактов нет: ожидался $out/array-aggregate.llvm.ll" >&2
    exit 1
fi

probe() {
    local name="$1" control="${2:-}"
    rm -rf "$work"; mkdir -p "$work"
    # Без `sanitize_address` ASan функцию не трогает - см. шапку.
    sed 's/ nounwind {/ nounwind sanitize_address {/' "$out/$name.llvm.ll" > "$work/prog.ll"
    if [ -n "$control" ]; then
        # Все чтения разом: за конец блока выходит **последняя** ячейка, и
        # подменять надо именно её - подмена первой осталась бы в границах.
        sed -i 's/\(%[A-Za-z0-9_.]*\) = load i96, ptr \([A-Za-z0-9_.%]*\), align 1/\1.wide = load i128, ptr \2, align 1\n  \1 = trunc i128 \1.wide to i96/' \
            "$work/prog.ll"
    fi
    "$ADAMAS_LLVM_BIN/llvm-as" "$work/prog.ll" -o "$work/prog.bc"
    "$ADAMAS_CLANG" -std=c11 -O1 -Xclang -disable-llvm-passes -emit-llvm -c \
        -I "$include" "$out/$name.llvm.support.c" -o "$work/support.bc"
    for source in "$root"/crates/adamas-runtime/c/*.c; do
        "$ADAMAS_CLANG" -std=c11 -O1 -Xclang -disable-llvm-passes -emit-llvm -c \
            -I "$include" "$source" -o "$work/$(basename "$source" .c).bc"
    done
    "$ADAMAS_LLVM_BIN/llvm-link" "$work"/*.bc -o "$work/all.bc" 2>/dev/null
    "$ADAMAS_LLVM_BIN/opt" -passes='asan' "$work/all.bc" -o "$work/asan.bc"
    local places
    places=$("$ADAMAS_LLVM_BIN/llvm-dis" "$work/asan.bc" -o - | grep -c '__asan_report' || true)
    "$ADAMAS_LLVM_BIN/llc" -O1 -filetype=obj -relocation-model=pic "$work/asan.bc" \
        -o "$work/asan.o"
    "$ADAMAS_CLANG" -fsanitize=address "$work/asan.o" -o "$work/asan.bin"
    if "$work/asan.bin" >/dev/null 2>"$work/err"; then
        printf '%-28s мест %-4s ASan молчит\n' "$name" "$places"
    else
        printf '%-28s мест %-4s ASan закричал: %s\n' "$name" "$places" \
            "$(grep -m1 -E 'SUMMARY|READ of size' "$work/err" || echo '(без строки)')"
    fi
}

if [ "${1:-}" = "--control" ]; then
    echo
    echo '== положительный контроль: `load i96` подменён на `load i128`'
    probe array-aggregate wide
    exit 0
fi

echo
echo "== честный выход эмиттера"
for name in "${NAMES[@]}"; do
    probe "$name"
done
