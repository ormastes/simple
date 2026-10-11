# Target 6 SCV snapshot MIR row types

Status: focused source repair; production native verification OPEN.

The admitted pure-Simple Stage 2 compiler (SHA-256 `e0e5a6cd522d6ee86b0dbb8e7cdd88cad21b3daa39d18b65b2ce163867e0eb06`) compiled `src/lib/scv/compile_snapshot.spl` with `SIMPLE_NO_STUB_FALLBACK=1`, `SIMPLE_LIB=src`, and `--format=smf`. The 122-module closure passed parse, HIR, and monomorphization but failed MIR.

- `compile_snapshot.spl` now gives inventory rows an explicit `[text]` type. The focused run then had 14 MIR errors and no unresolved `split` at the inventory row. Log: `build/mini_builds/item56_scv_snapshot_typed_rows_20261011.log`.
- `integrity.spl` now gives object-index rows an explicit `[SdnRow]` type. After a corrected syntax edit, the same focused closure reached MIR with 13 errors; the former `lib.scv.integrity` non-array `for-in` error was absent. Log: `build/mini_builds/item56_scv_snapshot_typed_rows_cycle3_20261011.log`.
- The intermediate second attempt stopped at parse because the edit accidentally contained a literal backslash-n. It was corrected before the final run. Log: `build/mini_builds/item56_scv_snapshot_typed_rows_cycle2_20261011.log`.

The 13 remaining MIR errors include enum payload matching/construction, unresolved `substring`, `release`, `trim`, and `get` methods, a multiple-wildcard match, and an untyped gzip Huffman iteration. No SMF output or passing native Item 6 test resulted. The three-cycle limit is exhausted for this focused compile in this session; do not promote this evidence to a warm compile or release PASS. Ordinary CLI V3 graph publication and matched p95/RSS cohorts remain open.
