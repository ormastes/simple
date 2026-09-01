#!/bin/sh
# $1 = compiler path, $2 = file, $3 = out tsv, $4 = tmp root, $5 = timeout secs
CC="$1"; F="$2"; OUT="$3"; TMPROOT="$4"; TMO="$5"
D="$TMPROOT/$$"
mkdir -p "$D"
LOG="$D/log"
timeout -s KILL "$TMO" "$CC" compile --format=smf -o "$D/o.smf" "$F" > "$LOG" 2>&1
rc=$?
step=$(grep -o 'step [0-9]/6' "$LOG" | tail -1)
err=$(grep -m1 -E '^(error|Error|thread .* panicked)' "$LOG" | head -c 400 | tr '\t\n' '  ')
[ -z "$err" ] && err=$(tail -3 "$LOG" | tr '\t\n' '  ' | head -c 400)
printf '%s\t%s\t%s\t%s\n' "$F" "$rc" "${step:-none}" "$err" >> "$OUT"
rm -rf "$D"
