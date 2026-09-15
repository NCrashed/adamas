#!/usr/bin/env bash
# Из чего состоит разрыв скалярной строки: потолок на C и свидетель
# переассоциации.
#
# Строка «скалярная арифметика» отстаёт от соседа на Rust в шесть раз, и это
# число само по себе не читается: оно не говорит, отстаёт понижение или
# отстаёт gcc. Здесь мерятся три точки, которых в стенде нет.
#
#   1. Тот же цикл руками на C, той же строкой сборки, что у понижения. Это
#      потолок: обогнать его понижение не может по построению.
#   2. Тот же цикл на Rust с множителем-литералом - точка стенда, повторённая
#      без стенда.
#   3. Он же с множителем из аргумента. Различие с (2) - ровно константность
#      множителя, и больше ничего.
#
# Если (3) садится на (1), а (2) остаётся внизу, то разрыв - это одна
# оптимизация LLVM: аффинную рекурсию `acc := acc*K + b` с **константным** K
# разворот раскладывает в `K^U` плюс линейный член, и цепочка из U умножений
# схлопывается в одно. Ни gcc, ни, значит, наше понижение этого не делают.
#
# Оценка - пол выборки, как и у стенда: помеха ко времени процесса только
# прибавляет. Привязка к ядру - параметром.
set -eu

TURNS="${TURNS:-50000000}"
CORE="${CORE:-8}"
RUNS="${RUNS:-9}"
K=6364136223846793005

DIR="$(mktemp -d)"
trap 'rm -rf "$DIR"' EXIT

cat > "$DIR/hand.c" <<EOF
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
/* Самовызов в хвосте - той же формы, какой цикл написан на Adamas. */
static uint64_t mix(uint64_t n, uint64_t acc) {
  if (n == 0) return acc;
  return mix(n - 1, acc * ${K}ULL + n);
}
int main(int argc, char **argv) {
  (void)argc;
  printf("%llu\n", (unsigned long long)mix(strtoull(argv[1], 0, 10), 0));
  return 0;
}
EOF

cat > "$DIR/mix.rs" <<EOF
fn main() {
    let mut argv = std::env::args().skip(1);
    let n: u64 = argv.next().unwrap().parse().unwrap();
    let k: u64 = argv.next().unwrap().parse().unwrap();
    let literal = argv.next().unwrap() == "literal";
    let (mut acc, mut left): (u64, u64) = (0, n);
    if literal {
        while left != 0 {
            acc = acc.wrapping_mul(${K}).wrapping_add(left);
            left -= 1;
        }
    } else {
        while left != 0 {
            acc = acc.wrapping_mul(k).wrapping_add(left);
            left -= 1;
        }
    }
    println!("{acc}");
}
EOF

# Строка сборки та же, что у стенда: `RELEASE` в `benches/harness/mod.rs` и
# профиль `release` этого репозитория (`lto = "thin"`, `codegen-units = 1`).
gcc -std=c11 -O2 -flto -fwrapv "$DIR/hand.c" -o "$DIR/hand"
rustc -O -C lto=thin -C codegen-units=1 "$DIR/mix.rs" -o "$DIR/mix" 2>/dev/null

floor() {
  local name="$1"; shift
  local best="" answer=""
  for _ in $(seq 1 "$RUNS"); do
    local start end elapsed
    start=$(date +%s%N)
    answer=$(taskset -c "$CORE" "$@")
    end=$(date +%s%N)
    elapsed=$(( (end - start) / 1000 ))
    if [ -z "$best" ] || [ "$elapsed" -lt "$best" ]; then best=$elapsed; fi
  done
  printf '%s.%03d мс — %s (ответ %s)\n' "$((best / 1000))" "$((best % 1000))" \
         "$name" "$answer"
}

echo "витков $TURNS, ядро $CORE, пол по $RUNS запускам"
floor "потолок: руками на C" "$DIR/hand" "$TURNS"
floor "сосед: множитель литералом" "$DIR/mix" "$TURNS" "$K" literal
floor "он же: множитель аргументом" "$DIR/mix" "$TURNS" "$K" runtime
