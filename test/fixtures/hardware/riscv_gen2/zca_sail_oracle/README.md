# Gen2 Zca independent oracle fixture

This directory contains exhaustive **classification-only** tables generated
from the pinned `riscv/sail-riscv` Zca decoder semantics. It does not contain
canonical 32-bit expansions and does not prove equivalence with Simple/HWIR.
Simple/HWIR decoder code never generates these files.

Format `simple-riscv-zca-oracle-v2` uses one tab-separated row per parcel in
strict `0000` through `FFFF` order:

```text
parcel  classification  canonical32  original_length_bytes  semantic_name
```

`classification` is `legal`, `illegal`, or `not-compressed`;
`canonical32` is always `--------` because the admitted extractor calls only
Sail's compressed-decoder match predicate. RV32 and RV64 each contain exactly
65,536 rows. Legal rows use semantic name `zca-classification-only`.

Workflow:

1. `scripts/tool/acquire-riscv-gen2-zca-oracle.shs`
2. Set `SAIL_EXECUTABLE` to Sail 0.20.1 and run
   `scripts/tool/build-riscv-gen2-zca-sail-classifier.shs`.
3. Update only the hashes in `oracle.lock` after reviewing the generated diff.
4. Run `scripts/check/check-riscv-gen2-zca-oracle.shs`.

The manifest records `qualification=false`, `canonical_expansion=false`, and
`exhaustive_equivalence=false`. `simple_classifier_comparison=not-run` remains
mandatory until a trustworthy canonical Simple classifier executable/API is
available. The tables prove exhaustive Sail classification coverage only.
