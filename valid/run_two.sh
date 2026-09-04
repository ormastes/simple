#!/bin/sh
S="$1"
D=/mnt/data/worktrees/phase1-validate-1
L="$D/valid/logs2/$(echo "$S" | tr '/' '_').log"
cd "$D"
export SIMPLE_TIMEOUT_SECONDS=0
export SIMPLE_BIN="$D/valid/phase1-simple"
timeout 900 ./valid/phase1-simple test "$S" > "$L" 2>&1
RC=$?
V=$(grep -m1 '^SPEC FILE VERDICT:' "$L"); [ -z "$V" ] && V="NOVERDICT"
printf '%s\trc=%s\t%s\n' "$S" "$RC" "$V" >> "$D/valid/results2.tsv"
