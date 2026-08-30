#!/bin/sh
S="$1"
D=/mnt/data/worktrees/phase1-validate-1
L="$D/valid/logs/$(echo "$S" | tr '/' '_').log"
cd "$D"
SIMPLE_TIMEOUT_SECONDS=0 timeout 600 ./valid/phase1-simple test "$S" > "$L" 2>&1
RC=$?
V=$(grep -m1 '^SPEC FILE VERDICT:' "$L")
if [ -z "$V" ]; then V="NOVERDICT"; fi
printf '%s\trc=%s\t%s\n' "$S" "$RC" "$V" >> "$D/valid/results.tsv"
