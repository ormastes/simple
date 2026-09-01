#!/bin/sh
cd /mnt/data/worktrees/phase1-validate-1
> valid/final.tsv
while read s; do
  L="valid/logs2/$(echo $s | tr '/' '_').log"
  P=$(sed 's/\x1b\[[0-9;]*m//g' "$L" 2>/dev/null)
  MSG=$(printf '%s' "$P" | grep -A1 '^[[:space:]]*✗' | grep -v '✗' | grep -v '^--' | sed 's/^[[:space:]]*//' | head -1)
  BEH=$(printf '%s' "$P" | grep -m1 '^[[:space:]]*✗' | sed 's/^[[:space:]]*✗ //')
  [ -z "$MSG" ] && MSG="(no assertion message)"
  C="G-behavioral-mismatch"
  case "$MSG" in
    *"expected # "*|*"expected use "*|*"expected //"*|*"expected fn "*) C="B-spec-source-text-drift";;
    "semantic: "*not\ found*|"semantic: unknown static method"*|"semantic: class"*"has no field"*|"semantic: undefined field"*|"semantic: function expects"*) C="B-spec-api-drift";;
    "semantic: panic: compile error:"*"does not support"*|*"not implemented"*|*"unimplemented"*) C="D-optional-feature-gated";;
    "semantic: "*) C="C-compiler-semantic-reject";;
  esac
  case "$P" in *"bin/simple: not found"*|*"nice: ‘bin/simple’"*) C="A-environment";; esac
  case "$P" in *"reason=parse-error"*) C="E-parse-error";; esac
  case "$P" in *"is a bootstrap seed only"*) : ;; esac
  printf '%s\t%s\t%s\t%s\n' "$C" "$s" "$BEH" "$MSG" >> valid/final.tsv
done < valid/failing2.txt
echo done > valid/cl3done.txt
