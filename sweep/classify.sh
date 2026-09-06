#!/bin/sh
# $1 = tsv
awk -F'\t' '{
  rc=$2; e=$4;
  gsub(/WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool\. */,"",e);
  gsub(/Build and use the pure-Simple bin\/simple instead\. */,"",e);
  gsub(/\[hir-cache\][^ ]* [^ ]* */,"",e);
  gsub(/src\/[A-Za-z0-9_\/.]+\.spl(:[0-9]+(:[0-9]+)?)?/,"<P>",e);
  gsub(/\/mnt\/data[^ ]*/,"<P>",e);
  gsub(/source_idx=[0-9]+/,"source_idx=<N>",e);
  gsub(/error_idx=[0-9]+/,"error_idx=<N>",e);
  gsub(/  +/," ",e);
  if (rc==0) sig="OK";
  else sig=substr(e,1,150);
  print rc"\t"sig;
}' "$1" | sort | uniq -c | sort -rn
