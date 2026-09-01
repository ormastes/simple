#!/bin/sh
cd /mnt/data/worktrees/phase1-validate-1
> valid/sigs2.tsv
while read s; do
  L="valid/logs/$(echo $s | tr '/' '_').log"
  MSG=$(sed 's/\x1b\[[0-9;]*m//g' "$L" 2>/dev/null | grep -A1 '^\s*✗' | grep -v '^\s*✗' | grep -v '^--' | sed 's/^[[:space:]]*//' | head -1)
  BEH=$(sed 's/\x1b\[[0-9;]*m//g' "$L" 2>/dev/null | grep -m1 '^\s*✗' | sed 's/^[[:space:]]*✗ //')
  [ -z "$MSG" ] && MSG="(no assertion message)"
  printf '%s\t%s\t%s\n' "$s" "$BEH" "$MSG" >> valid/sigs2.tsv
done < valid/failing.txt
echo done > valid/sig2done.txt
