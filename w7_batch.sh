#!/bin/sh
# w7_batch.sh <start_line> <end_line>  — processes .w7.txt lines start..end (1-based, excluding the count line)
# Usage: sh w7_batch.sh 2 21
cd /tmp/mod14 || exit 1
S=/mnt/data/worktrees/simple-main/bin/simple
mkdir -p .w7log
if [ -n "$LIST" ]; then cat "$LIST"; else sed -n "${1},${2}p" .w7.txt; fi | while read -r f; do
  [ -f "$f" ] || { echo "$f MISSING" >> .w7skip.txt; continue; }
  grep -q "^$f\$" .w7done.txt 2>/dev/null && continue
  b=$(timeout 300 $S test --no-session-daemon "$f" 2>&1 | grep "^Results:" | tail -1)
  node w7_transform.js "$f" >/dev/null 2>&1 || { git checkout -- "$f"; echo "$f TRANSFORM_ERROR" >> .w7skip.txt; continue; }
  probe=$(timeout 300 $S probe_sspec_scores.spl "$f" 2>/dev/null | tail -1)
  eff=$(echo "$probe" | awk -F'\t' '{print $2}')
  a=$(timeout 300 $S test --no-session-daemon "$f" 2>&1 | grep "^Results:" | tail -1)
  bf=$(echo "$b" | sed 's/.* \([0-9]*\) failed.*/\1/'); bp=$(echo "$b" | sed 's/.* \([0-9]*\) passed.*/\1/')
  af=$(echo "$a" | sed 's/.* \([0-9]*\) failed.*/\1/'); ap=$(echo "$a" | sed 's/.* \([0-9]*\) passed.*/\1/')
  if [ -z "$a" ]; then
    git checkout -- "$f"; echo "$f TEST_TIMEOUT_OR_CRASH after=$a before=$b" >> .w7skip.txt; continue
  fi
  if [ "$bf" != "$af" ] || [ "$bp" != "$ap" ]; then
    git checkout -- "$f"; echo "$f RESULT_CHANGED before=[$b] after=[$a]" >> .w7skip.txt; continue
  fi
  if [ "$af" != "0" ]; then
    echo "$f ALREADY_RED [$a]" >> .w7red.txt
  fi
  if [ "$eff" -gt 80 ] 2>/dev/null; then
    echo "$f" >> .w7done.txt; echo "$f eff=$eff $a" >> .w7log/ok.log
  else
    if grep -qE "expect\((source\.contains|file_read\()|assert\((source\.contains|file_read\()|source text oracle" "$f"; then
      echo "$f eff=$eff blocker=[SSDOC-ORA-002 source-inspection oracle; unfixable without changing assertions]" >> .w7skip.txt
    else
      blk=$(timeout 300 $S /mnt/data/worktrees/simple-main/src/app/sspec_maintain/main.spl scan "$f" 2>&1 | grep "blocker SSDOC" | head -1 | grep -o 'blocker SSDOC-[A-Z0-9-]*' | tr '\n' ',')
      echo "$f eff=$eff blocker=[$blk]" >> .w7skip.txt
    fi
  fi
done
echo "BATCH_DONE $1-$2 done=$(wc -l < .w7done.txt 2>/dev/null || echo 0) skip=$(wc -l < .w7skip.txt 2>/dev/null || echo 0) red=$(wc -l < .w7red.txt 2>/dev/null || echo 0)"
