#!/bin/sh
# Verify (test + score) every rewritten spec; record done/skip/red/partial.
cd /tmp/mod10
BIN=/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
SCOREBIN="cd /mnt/data/worktrees/simple-main && bin/simple probe_sspec_scores.spl"
while read -r f; do
  [ -f "$f" ] || continue
  grep -q 'fn check(condition: bool):' "$f" && { echo "$f" >> .w6skip.txt; continue; }
  grep -qx "$f" .w6done.txt 2>/dev/null && continue
  v=$(timeout 90 $BIN test --no-session-daemon "$f" 2>&1 | grep -c 'outcome=OK')
  if [ "$v" != 1 ]; then
    echo "$f" >> .w6red.txt
    continue
  fi
  s=$(cd /mnt/data/worktrees/simple-main && timeout 120 bin/simple probe_sspec_scores.spl "/tmp/mod10/$f" 2>/dev/null | tail -1 | cut -f2)
  if [ -n "$s" ] && [ "$s" -gt 80 ] 2>/dev/null; then
    echo "$f" >> .w6done.txt
  else
    echo "$f $s" >> .w6partial.txt
  fi
done < .w6.txt
echo VERIFY_COMPLETE
