# GZIP native return types rejected by the HIR return-type interface

- id: gzip_native_rti_untyped_results_2026-10-31
- status: LZ77 declaration annotations authored; runtime and native
  qualification UNRUN; `gzip_analyze_data` remains blocked for user decision

## Evidence and provenance

BuildRunner source `3e4dfcdce0d375dbe3c92ee63d891e84f70cc795` with producer
`9633bf0af8b70d5f0324a35b244b3d08a62cdbcd1f8a3cd2aff246620f572dbd` failed
module-local RTI checks for `gzip_analyze_data` and `lz77_compress`. The 312
failed shard claims are downstream consequences, not 312 independent causes.
Logs and caches under `/tmp/buildrunner-newproducer-attempt2-20261031` are
read-only and were not changed.

The inference scan under the ambient bootstrap reports `Any` for unresolved
unannotated returns. RTI correctly refuses `Any` rather than publishing an
unknown declaration contract. For LZ77, the established API is an outer array
of token rows `[kind, literal-or-distance, length]`, with each token row an
integer array. Nil and empty input return an empty outer array. The narrow
source repair is only `lz77_compress(data, level) -> [[i64]]` and the existing
local `tokens: [[i64]]`; input acceptance, byte rows, algorithm, level policy,
and nil/empty behavior remain the same.

## Separate unresolved issues

`gzip_analyze_data` is **BLOCKED** awaiting the user's choice. Its current
shape includes nil and the heterogeneous mutable array `[i64, i64, f64,
[i64]]`; it must not be silently changed to a tuple or record. Its source and
the RTI guard/compiler are outside this repair.

The older `seed_native_gzip_deflate_miscompile_2026-10-19` report concerns
untyped byte boxing and optional-array gaps. The LZ77 return annotation does
not claim to repair those runtime semantics. Native output is not qualified.

## Authored evidence and qualification

`test/01_unit/lib/nogc_sync_mut/compression/gzip_lz77_return_contract_spec.spl`
uses the real LZ77 implementation to cover nil and empty input, exact literal
rows for boundary bytes, exact repeated-match rows at levels 1/6/9, and mutable
array-row/outer-list behavior. It also reads the actual production LZ77 and
GZIP types sources, builds module surfaces, lowers the real module, and asks
`rti_rows_from_hir_v1` for the declared nested array-of-i64 return. The spec is
authored but **UNRUN**; no RED/GREEN result is claimed.

Native behavior requires later qualification on an admitted producer against
the frozen repaired sources. Neither the RTI declaration nor these unrun tests
establish native behavior or close the older byte-boxing/optional-array bug.
