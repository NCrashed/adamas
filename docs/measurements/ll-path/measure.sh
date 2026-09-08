#!/usr/bin/env bash
set -uo pipefail
# Промежуточные файлы крупные (до 47 МБ на .ll) — работаем во временном каталоге,
# репозиторий не засоряем.
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cd "$work"

# лучшее из 3 прогонов, в миллисекундах
best() {
  local b=999999 t s e
  for _ in 1 2 3; do
    s=$(date +%s%N); "$@" >/dev/null 2>&1; e=$(date +%s%N)
    t=$(( (e - s) / 1000000 ))
    (( t < b )) && b=$t
  done
  echo "$b"
}

printf '%-8s %9s %9s %9s %9s %9s %9s   %s\n' \
  функций .ll-МБ .bc-МБ as-мс dis-мс opt-мс llc-мс "доля разбора"

for n in 200 2000 20000; do
  bash "$here/gen.sh" "$n" > s$n.c
  # -disable-O0-optnone: иначе clang вешает optnone и opt -O2 ничего не делает
  clang -O0 -Xclang -disable-O0-optnone -S -emit-llvm s$n.c -o s$n.ll 2>/dev/null

  as=$(best llvm-as s$n.ll -o s$n.bc)
  dis=$(best llvm-dis s$n.bc -o /dev/null)
  opt=$(best opt -O2 s$n.bc -o o$n.bc)
  llc=$(best llc -O2 -filetype=obj o$n.bc -o o$n.o)

  llmb=$(awk "BEGIN{printf \"%.1f\", $(stat -c%s s$n.ll)/1048576}")
  bcmb=$(awk "BEGIN{printf \"%.1f\", $(stat -c%s s$n.bc)/1048576}")
  share=$(awk "BEGIN{printf \"%.1f%%\", 100*$as/($as+$opt+$llc)}")

  printf '%-8s %9s %9s %9s %9s %9s %9s   %s\n' \
    "$n" "$llmb" "$bcmb" "$as" "$dis" "$opt" "$llc" "$share"
done
