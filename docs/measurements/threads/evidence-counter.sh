#!/usr/bin/env bash
# Чего стоит гибридный счётчик вектора evidence (§5.1, трек E волны 3).
#
# Счётчик вектора стал гибридным - ветвь по флагу плюс вынесенная за
# `noinline, cold` атомарная половина, - потому что вектор файбера уезжает на
# чужой воркер вместе с его кадрами: дупает его `frame_alloc` на одном потоке,
# дропает `frame_free` на другом.
#
# Нагрузками из таблицы разрыва это не мерится, и не потому, что лень: **ни
# одна из пяти кадра не ставит вовсе**. Проверяется это той же командой, что и
# меряет:
#
#   grep -c adamas_kont_push <порождённый C нагрузки>   # ноль у всех пяти
#
# Мерено поэтому на самой кадроёмкой из доступных - хендлерном стенде
# `benches/native.rs`. Стороны: счётчик как был (голый `+=`) против гибридного.
#
# Оценка - пол выборки, стороны чередуются в одном окне: тихой машины нет.
set -eu

ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
CORE="${CORE:-8}"
ROUNDS="${ROUNDS:-9}"

PROG="${PROG:-$(ls "$ROOT"/target/*/build/adamas-codegen-*/out/bench-native/handled16.c 2>/dev/null | head -1)}"
if [ -z "$PROG" ]; then
    echo "нет порождённого handled16.c: сперва 'cargo bench -p adamas-codegen --bench native'" >&2
    exit 1
fi

DIR="$(mktemp -d)"
trap 'rm -rf "$DIR"' EXIT

HYBRID_DUP='    adamas_header *header = adamas_header_of(evidence);
    if ((header->flags & ADAMAS_FLAG_SHARED) != 0) {
        evidence_dup_shared(header);
        return evidence;
    }
    header->rc += 1;
    return evidence;'
PLAIN_DUP='    adamas_header_of(evidence)->rc += 1;
    return evidence;'
HYBRID_DROP='    adamas_header *header = adamas_header_of(evidence);
    if ((header->flags & ADAMAS_FLAG_SHARED) != 0) {
        if (evidence_released_shared(header)) {
            adamas_block_free(evidence);
        }
        return;
    }
    if (header->rc == 0) {'
PLAIN_DROP='    adamas_header *header = adamas_header_of(evidence);
    if (header->rc == 0) {'

swap() {
    ADAMAS_FROM="$2" ADAMAS_TO="$3" perl -0pi -e '
        my ($from, $to) = ($ENV{ADAMAS_FROM}, $ENV{ADAMAS_TO});
        my $at = index($_, $from);
        die "подстрока не нашлась\n" if $at < 0;
        substr($_, $at, length($from)) = $to;
    ' "$1"
}

for side in now before; do
    cp -r "$ROOT/crates/adamas-runtime/c" "$DIR/$side"
    if [ "$side" = before ]; then
        swap "$DIR/$side/evidence.c" "$HYBRID_DUP" "$PLAIN_DUP"
        swap "$DIR/$side/evidence.c" "$HYBRID_DROP" "$PLAIN_DROP"
    fi
    gcc -std=c11 -O2 -flto -fwrapv -ffp-contract=off -w \
        -I "$ROOT/crates/adamas-runtime/include" "$PROG" "$DIR/$side"/*.c \
        -o "$DIR/$side.bin"
done

declare -A floor=([now]=999999999 [before]=999999999)
for _ in $(seq "$ROUNDS"); do
    for side in now before; do
        start=$(date +%s%N)
        taskset -c "$CORE" "$DIR/$side.bin" >/dev/null 2>&1
        end=$(date +%s%N)
        took=$(( (end - start) / 1000 ))
        [ "$took" -lt "${floor[$side]}" ] && floor[$side]=$took
    done
done

printf 'пол: гибридный %s мкс, голый %s\n' "${floor[now]}" "${floor[before]}"
awk -v a="${floor[now]}" -v b="${floor[before]}" 'BEGIN{
    printf "гибридный/голый = %.4f\n", a/b
}'
