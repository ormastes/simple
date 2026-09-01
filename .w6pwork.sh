#!/bin/sh
# One worker: verify a single spec (test + score). Usage: .w6pwork.sh <file>
cd /tmp/mod10
f="$1"
BIN=/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
v=$(timeout 120 $BIN test --no-session-daemon "$f" 2>&1 | grep -c 'outcome=OK')
if [ "$v" != 1 ]; then
  echo "$f" >> .w6red.txt
  exit 0
fi
s=$(cd /mnt/data/worktrees/simple-main && timeout 180 bin/simple probe_sspec_scores.spl "/tmp/mod10/$f" 2>/dev/null | tail -1 | cut -f2)
if [ -n "$s" ] && [ "$s" -gt 80 ] 2>/dev/null; then
  echo "$f" >> .w6done.txt
else
  echo "$f $s" >> .w6partial.txt
fi
