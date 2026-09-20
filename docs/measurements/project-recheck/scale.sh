#!/usr/bin/env bash
# Полная перепроверка проекта: от чего растёт цена - от файлов или от кода.
#
# План волны 2 Фазы 9 умножил 36 мс (капстоун в 944 строки, один файл) на
# десять файлов и получил ~360 мс - больше бюджета интерактивности. Умножение
# шло **по файлам**, и этот стенд проверяет именно множитель: проект корпуса
# (`tests/golden/project`, 10 файлов) размножается K раз, и каждая копия -
# настоящая библиотека со своими девятью модулями, подключающими друг друга.
#
# Имена программы (класс, метод, эффект, операция) объявляются без
# квалификации: у двух копий библиотеки они столкнулись бы, поэтому копия
# получает свой номер к каждому такому имени. Всё прочее - буквально те же
# файлы.
#
# Вход K-го проекта подключает по три модуля каждой копии (`Order`, `Effect`,
# `Show`), а те тянут остальные шесть: проверяется весь код, а не заголовки.
#
# Оценка - пол десяти запусков. Мерится `adamas check` процессом, то есть
# вместе со стартом драйвера (2,0 мс): именно столько ждёт человек в терминале.
set -eu

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/../../.." && pwd)"
SRC="${SRC:-$REPO/tests/golden/project}"
BIN="${BIN:-$REPO/target/release/adamas}"
COPIES="${COPIES:-1 2 4 8 16}"
RUNS="${RUNS:-10}"

if [ ! -x "$BIN" ]; then
  echo "нет драйвера: $BIN (cargo build --release -p adamas-cli)" >&2
  exit 1
fi

OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT

# Имена, которые объявляются без квалификации (§4.4): их копия переименовывает.
GLOBALS="Eqv eq Functor map Applicative pure ap Monad bind Ord lte Fail bail Emit emit"

copy() { # каталог номер
  local dir="$1" n="$2" file base g
  mkdir -p "$dir/M$n"
  for file in "$SRC"/Std/*.adamas; do
    base="$(basename "$file")"
    sed -e "s/\bStd\./M$n./g" "$file" > "$dir/M$n/$base"
    for g in $GLOBALS; do
      sed -i -e "s/\b$g\b/$g$n/g" "$dir/M$n/$base"
    done
  done
}

entry() { # каталог число_копий
  local dir="$1" k="$2" n
  : > "$dir/main.adamas"
  for n in $(seq 1 "$k"); do
    printf 'import M%s.Order\nimport M%s.Effect\nimport M%s.Show\n' "$n" "$n" "$n" \
      >> "$dir/main.adamas"
  done
  printf '\nimport M1.Base (Nat, Zero, Succ)\n\nmain : Nat\nmain = Succ Zero\n' \
    >> "$dir/main.adamas"
}

floor() { # путь_ко_входу -> микросекунды
  local entry="$1" best=999999999 i start end took
  for i in $(seq 1 "$RUNS"); do
    start=$(date +%s%N)
    "$BIN" check "$entry" > /dev/null
    end=$(date +%s%N)
    took=$(( (end - start) / 1000 ))
    if [ "$took" -lt "$best" ]; then best=$took; fi
  done
  echo "$best"
}

measured() { # заголовок вход файлы строки
  local best
  best=$(floor "$2")
  printf '%-7s %-8s %-8s %s.%03d мс\n' "$1" "$3" "$4" \
    "$((best / 1000))" "$((best % 1000))"
}

# Первая точка отвечает на вопрос прямо: одна и та же библиотека, разложенная
# на два файла и на десять. Строк почти поровну (343 против 328 - разница в
# шапках модулей), файлов в пять раз больше.
echo "та же библиотека, разное число файлов:"
printf '%-7s %-8s %-8s %s\n' "-" "файлов" "строк" "полная перепроверка"
measured "-" "$REPO/tests/golden/eval/prelude.adamas" 2 343
measured "-" "$SRC/main.adamas" 10 328
echo

echo "та же раскладка, разное число копий библиотеки:"
printf '%-7s %-8s %-8s %s\n' "копий" "файлов" "строк" "полная перепроверка"

for k in $COPIES; do
  dir="$OUT/k$k"
  rm -rf "$dir"; mkdir -p "$dir"
  for n in $(seq 1 "$k"); do copy "$dir" "$n"; done
  entry "$dir" "$k"
  if ! "$BIN" check "$dir/main.adamas" > "$OUT/answer"; then
    echo "K=$k: проверка отказала" >&2
    cat "$OUT/answer" >&2
    exit 1
  fi
  files=$(find "$dir" -name '*.adamas' | wc -l)
  lines=$(cat $(find "$dir" -name '*.adamas') | wc -l)
  best=$(floor "$dir/main.adamas")
  printf '%-7s %-8s %-8s %s.%03d мс\n' "$k" "$files" "$lines" \
    "$((best / 1000))" "$((best % 1000))"
done
