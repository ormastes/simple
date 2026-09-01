#!/bin/sh
# process one spec: baseline -> transform -> test -> documentize -> score
BIN=/mnt/data/worktrees/simple-main/bin/simple
cd /tmp/mod15 || exit 9
f="$1"
resline() { timeout 300 $BIN test --no-session-daemon "$f" 2>/dev/null | grep -E '^Results:' | tail -1; }

base=$(resline)
bp=$(echo "$base" | sed -n 's/.* \([0-9]*\) passed.*/\1/p'); bf=$(echo "$base" | sed -n 's/.* \([0-9]*\) failed.*/\1/p')
[ -z "$bp" ] && bp=-1; [ -z "$bf" ] && bf=-1

python3 .w7xform.py "$f" || { echo "XFORM_ERR $f"; git checkout -- "$f" 2>/dev/null; exit 0; }

after=$(resline)
ap=$(echo "$after" | sed -n 's/.* \([0-9]*\) passed.*/\1/p'); af=$(echo "$after" | sed -n 's/.* \([0-9]*\) failed.*/\1/p')
[ -z "$ap" ] && ap=-1; [ -z "$af" ] && af=-1

if [ "$bp" = "-1" ]; then
  echo "BASELINE_BAD $f ($base)" >> .w7skip.txt
  git checkout -- "$f" 2>/dev/null; exit 0
fi
if [ "$af" != "$bf" ] || [ "$ap" != "$bp" ]; then
  echo "TEST_REGRESS $f base=$bp/$bf after=$ap/$af" >> .w7skip.txt
  git checkout -- "$f" 2>/dev/null; exit 0
fi
[ "$bf" -gt 0 ] && echo "$f base=$bp/$bf" >> .w7red.txt

timeout 300 $BIN src/app/sspec_maintain/main.spl documentize "$f" >/dev/null 2>&1
mirror="doc/06_spec/${f#test/}"; mirror="${mirror%.spl}.md"
score=$(timeout 300 $BIN probe_sspec_scores.spl "$f" 2>/dev/null | tail -1 | cut -f2)
if [ -n "$score" ] && [ "$score" -gt 80 ] 2>/dev/null; then
  echo "$f" >> .w7done.txt

else
  echo "LOW_SCORE $f score=${score:-none} scan:" >> .w7skip.txt
  timeout 300 $BIN src/app/sspec_maintain/main.spl scan "$f" 2>/dev/null | grep -iE "blocker SSDOC|narrative=" | head -2 >> .w7skip.txt
  git checkout -- "$f" 2>/dev/null
  git checkout -- "$mirror" 2>/dev/null
  git ls-files --error-unmatch "$mirror" >/dev/null 2>&1 || rm -f "$mirror"
fi
exit 0
