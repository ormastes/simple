#!/bin/sh
CC="$1"; F="$2"; OUT="$3"; TMPROOT="$4"; TMO="$5"
D="$TMPROOT/$$"
mkdir -p "$D"
LOG="$D/log"
SIMPLE_HIR_CACHE=0 SIMPLE_TIMEOUT_SECONDS=0 timeout -s KILL "$TMO" "$CC" compile --format=smf -o "$D/o.smf" "$F" > "$LOG" 2>&1
rc=$?
step=$(grep -o 'step [0-9]/6' "$LOG" | tail -1)
err=$(grep -m1 -E '^(error|Error|.*module surface promotion failed|.*[Uu]nresolved name|.*panicked)' "$LOG" | head -c 400 | tr '\t\n' '  ')
[ -z "$err" ] && err=$(grep -v '^\[build\]' "$LOG" | tail -3 | tr '\t\n' '  ' | head -c 400)
printf '%s\t%s\t%s\t%s\n' "$F" "$rc" "${step:-none}" "$err" >> "$OUT"
rm -rf "$D"
