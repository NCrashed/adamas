#!/usr/bin/env bash
# Прогоняет свидетель эквивалентности над демо заданной ревизии.
#
#   run.sh РЕВИЗИЯ before.adamas|after.adamas [c|llvm]
#
# Запускать внутри `nix develop`: сборке нужны SDL2 и цепочка LLVM.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
adamas=${ADAMAS:-$root/target/debug/adamas}
rev=$1
harness=$here/$2
backend=${3:-c}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
git -C "$root" archive "$rev" demo/asteroids | tar -x -C "$work"
cd "$work/demo/asteroids"
sed -i '/^main : Int32$/,$d' Main.adamas
grep -q 'SDL_VideoInit' Main.adamas ||
  sed -i 's/^import Sdl.Raw (Unit, Foreign, /import Sdl.Raw (Unit, Foreign, SDL_VideoInit, /' Main.adamas
cat "$harness" >> Main.adamas
for m in sc0 sc0lives sc1 sc1score sc1level sc2 sc3 sc3level "runForeign body2"; do
  sed -i '$d' Main.adamas
  echo "main = $m" >> Main.adamas
  echo "$m: $("$adamas" run --backend "$backend" . 2>&1 | tail -2 | tr '\n' ' ')"
done
