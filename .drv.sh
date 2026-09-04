#!/bin/bash
# driver: args = target files. Prints one line per file.
cd /tmp/mod7 || exit 1
SIM=/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
PROBE=/mnt/data/worktrees/simple-main/probe_sspec_scores.spl
touch .done.txt
for f in "$@"; do
  [ -f "$f" ] || { echo "$f MISSING"; continue; }
  grep -qx "$f" .done.txt && { echo "$f DONE_ALREADY"; continue; }
  base=$(timeout 240 $SIM test "$f" 2>/dev/null | grep -E 'SPEC FILE VERDICT|^Results:' | tail -1)
  twin=$(printf '%s' "$f" | sed -e 's|^test/01_unit/|test/unit/|' -e 's|^test/00_formal_verification/|test/formal_verification/|' -e 's|^test/02_integration/|test/integration/|' -e 's|^test/03_system/|test/system/|' -e 's|^test/unit/|test/01_unit/|' -e 's|^test/formal_verification/|test/00_formal_verification/|' -e 's|^test/integration/|test/02_integration/|' -e 's|^test/system/|test/03_system/|')
  files="$f"
  tw=""
  if [ "$twin" != "$f" ] && [ -f "$twin" ]; then files="$f $twin"; tw="$twin"; fi
  identical_before=no; [ -n "$tw" ] && cmp -s "$f" "$tw" && identical_before=yes
  tbase=""; [ -n "$tw" ] && [ "$identical_before" = no ] && tbase=$(timeout 240 $SIM test "$twin" 2>/dev/null | grep -E 'SPEC FILE VERDICT|^Results:' | tail -1)
  python3 .mod.py $files >/dev/null 2>&1
  after=$(timeout 240 $SIM test "$f" 2>/dev/null | grep -E 'SPEC FILE VERDICT|^Results:' | tail -1)
  tafter=""; [ -n "$tbase" ] && tafter=$(timeout 240 $SIM test "$twin" 2>/dev/null | grep -E 'SPEC FILE VERDICT|^Results:' | tail -1)
  twflag=""; [ -n "$tbase" ] && [ "$tbase" != "$tafter" ] && twflag=1
  score=$(timeout 180 $SIM $PROBE "/tmp/mod7/$f" 2>&1 | tail -1 | awk '{print $2}')
  verdict=KEEP
  if [ "$base" = "$after" ]; then :; else verdict=REVERT_CNT; fi
  case "$score" in ''|*[!0-9]*) verdict=REVERT_SCORE;; *) [ "$score" -gt 80 ] || verdict=REVERT_SCORE;; esac
  if [ "$identical_before" = yes ] && [ -n "$tw" ] && ! cmp -s "$f" "$tw"; then verdict=REVERT_TWIN; fi
  [ -n "$twflag" ] && verdict=REVERT_TWIN_CNT
  if [ "$verdict" != KEEP ]; then
    git checkout -- $files
    echo "$f $verdict (base='$base' after='$after' score='$score')"
    continue
  fi
  # verify twin still passes if it was pre-modified independently? identical twins already covered
  echo "$f" >> .done.txt
  if [ -n "$tw" ]; then
    grep -qx "$tw" .done.txt || echo "$tw" >> .done.txt
  fi
  echo "$f KEEP score=$score ($after)"
done
