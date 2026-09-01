#!/bin/bash
# wave runner: fast-path probe, else drv.sh. args: max_files
cd /tmp/mod7 || exit 1
SIM=/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
PROBE=/mnt/data/worktrees/simple-main/probe_sspec_scores.spl
max=${1:-5}
n=0
for f in $(cat .targets.txt); do
  [ $n -ge $max ] && break
  [ -f "$f" ] || continue
  grep -qx "$f" .done.txt && continue
  grep -qx "$f" .skip.txt 2>/dev/null && continue
  s=$(timeout 180 $SIM $PROBE "/tmp/mod7/$f" 2>&1 | tail -1 | awk '{print $2}')
  case "$s" in ''|*[!0-9]*) ;; *) if [ "$s" -gt 80 ]; then echo "$f FASTPATH score=$s"; echo "$f" >> .done.txt; n=$((n+1)); continue; fi;; esac
  sh .drv.sh "$f"
  grep -qx "$f" .done.txt || echo "$f" >> .skip.txt
  n=$((n+1))
done
