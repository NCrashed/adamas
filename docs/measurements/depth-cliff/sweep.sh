#!/usr/bin/env bash
# Перебор глубины по форме и стадии. Обрыв стека роняет процесс целиком,
# поэтому каждый шаг - свой процесс, а вердикт читается кодом возврата:
# 0 - прошло либо названный отказ, 134 - `stack overflow, aborting`.
#
#   sweep.sh <стек-в-KiB> <форма> <стадия> <N>...
#
# Стенд - `depth_probe.rs` рядом: копируется в `crates/adamas-cli/examples/`
# и собирается `cargo build --example depth_probe -p adamas-cli`.
P=${PROBE:-target/debug/examples/depth_probe}
KIB=$1
FORM=$2
STAGE=$3
shift 3
for N in "$@"; do
  OUT=$("$P" "$KIB" "$FORM" "$N" "$STAGE" 2>&1)
  CODE=$?
  printf '%s %s %s N=%s -> code=%s %s\n' "$KIB" "$FORM" "$STAGE" "$N" "$CODE" "${OUT:0:120}"
done
