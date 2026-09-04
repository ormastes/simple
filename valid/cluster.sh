#!/bin/sh
cd /mnt/data/worktrees/phase1-validate-1
awk -F'\t' '$3 ~ /outcome=ERROR/ || $3=="NOVERDICT" || $3 !~ /outcome=OK/ {print $1}' valid/results.tsv > valid/failing.txt
> valid/sigs.tsv
while read s; do
  L="valid/logs/$(echo $s | tr '/' '_').log"
  SIG=$(grep -aoE "Unknown variable: [A-Za-z_0-9]+|Undefined (function|variable|method|type|module)[^\"]{0,40}|Unregistered extern [A-Za-z_0-9]+|No method '[^']+'|Parse error[^\"]{0,60}|Unexpected token[^\"]{0,40}|Type mismatch[^\"]{0,50}|not implemented[^\"]{0,40}|unimplemented[^\"]{0,40}|TODO[^\"]{0,30}|Segmentation fault|panicked at [^\"]{0,50}|command not found|No such file or directory[^\"]{0,40}|expected [^\"]{0,40} but got [^\"]{0,30}|Expected [^\"]{0,40} got [^\"]{0,30}|assertion failed[^\"]{0,50}" "$L" 2>/dev/null | head -1)
  [ -z "$SIG" ] && SIG=$(grep -aE '^\s+(✗|FAIL)' "$L" | head -1 | cut -c1-120)
  [ -z "$SIG" ] && SIG="UNCLASSIFIED"
  printf '%s\t%s\n' "$s" "$SIG" >> valid/sigs.tsv
done < valid/failing.txt
echo "SIGDONE" > valid/sigdone.txt
