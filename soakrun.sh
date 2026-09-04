#!/bin/sh
# usage: soakrun.sh <N> <dir>
N=$1; D=$2
export SIMPLE_TIMEOUT_SECONDS=0
rm -rf "$D"; mkdir -p "$D"; cd "$D" || exit 1
S=/mnt/data/soak-3450520/bin/simple
M=/mnt/data/soak-3450520/src/app/scv/main.spl
"$S" run "$M" init >/dev/null 2>&1
T0=$(date +%s)
"$S" run "$M" pack-soak-v2 "$N" 2>&1 | grep -Ev '^\[|^ *[0-9]+ \||^ *\| |^Use explicit|^Example:|^$' | tail -5
T1=$(date +%s)
echo "WALL_SECONDS=$((T1-T0)) N=$N"
