#!/bin/sh
# Periodically commit newly verified spec files (with twin sync) in batches.
cd /tmp/mod10
B=0
while true; do
  if [ -f .w6done.txt ] && [ $(wc -l < .w6done.txt) -gt 0 ]; then
    files=""
    n=0
    while read -r f; do
      grep -qx "$f" .w6committed.txt 2>/dev/null && continue
      files="$files $f"
      t="test/unit/${f#test/01_unit/}"
      if [ -f "$t" ]; then
        if [ "$(git show HEAD:"$t" 2>/dev/null | md5sum)" = "$(git show HEAD:"$f" 2>/dev/null | md5sum)" ]; then
          cp "$f" "$t"; files="$files $t"
        fi
      fi
      echo "$f" >> .w6committed.txt
      n=$((n+1))
      [ $n -ge 25 ] && break
    done < .w6done.txt
    if [ -n "$files" ]; then
      B=$((B+1))
      git add $files && git commit -q -m "test(sspec): wave-6 real oracles — batch $((B+1)) (auto-commit of verified specs)" || true
    fi
  fi
  if grep -q VERIFY_COMPLETE .w6verify.out 2>/dev/null; then
    # one final sweep
    files=""
    while read -r f; do
      grep -qx "$f" .w6committed.txt 2>/dev/null && continue
      files="$files $f"; echo "$f" >> .w6committed.txt
    done < .w6done.txt
    [ -n "$files" ] && { git add $files && git commit -q -m "test(sspec): wave-6 real oracles — final sweep"; }
    echo COMMITTER_DONE batches=$B
    exit 0
  fi
  sleep 300
done
