#!/bin/sh
cd /mnt/data/worktrees/phase1-validate-1
> valid/classified.tsv
while IFS="	" read s beh msg; do
  L="valid/logs/$(echo $s | tr '/' '_').log"
  P=$(sed 's/\x1b\[[0-9;]*m//g' "$L" 2>/dev/null)
  C="Z-other"
  case "$P" in
    *"bin/simple: not found"*|*"nice: ‘bin/simple’"*|*"failed to run command ‘bin/simple’"*|*"bin/simple: No such file"*) C="ENV-missing-bin-simple";;
  esac
  if [ "$C" = "Z-other" ]; then
   case "$msg" in
    *"expected # "*|*"expected use "*|*"expected //"*) C="SPEC-source-text-drift";;
    "semantic:"*) C="COMPILER-semantic-error";;
    *"does not support async"*|*"not implemented"*|*"unimplemented"*) C="OPT-unimplemented-gated";;
   esac
  fi
  if [ "$C" = "Z-other" ]; then
    case "$P" in
      *"Segmentation fault"*) C="CRASH-segfault";;
      *"Unknown variable: next"*) C="COMPILER-generator-lowering";;
      *"Unregistered extern"*) C="COMPILER-unbacked-extern";;
      *"semantic:"*) C="COMPILER-semantic-error";;
      *"Unexpected token"*|*"Parse error"*) C="COMPILER-parse-error";;
    esac
  fi
  if [ "$C" = "Z-other" ]; then
    case "$msg" in
      "expected "*to*equal*|"assert_"*|"expected true"*|"expected false"*|*"to be greater"*|*"to be nil"*|*"to contain"*) C="ASSERT-behavioral-mismatch";;
      "(no assertion message)") C="NOMSG-runner-level";;
    esac
  fi
  printf '%s\t%s\t%s\t%s\n' "$C" "$s" "$beh" "$msg" >> valid/classified.tsv
done < valid/sigs2.tsv
echo done > valid/classdone.txt
