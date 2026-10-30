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

## Precise heterogeneous array and compile-only closure audit

The language HIR contains `HirTypeKind.Union(members)` in
`src/compiler/20.hir/hir_types.spl`. This does not make a union element
representable in RTI v1: `RtType` has no union term, and
`rti_term_of_hir_type` recursively converts array/optional elements without a
Union case. A nullable array of the precise integer, float and integer-array
alternatives would still reach E-RTI-007. `ReturnTypeEntry.Union` describes
top-level declaration alternatives, not an array element; instantiation
requires selecting an arm. `[Any]` also recursively fails the existing guard.
No annotation-only compatible repair was established.

A compatible compiler repair requires a deliberate representation contract:
recursive union RTI serialization, canonicalization, substitution and binding;
matching HIR-to-MIR tagged-value representation; and correct boxing/unboxing
for integer, float and nested-array values on reads, writes and mutation.
It must preserve nil, indexing and mutable-array behavior. Merely publishing
a new RTI term without implementing those consumers is insufficient. Required
qualification includes real-source RTI publication, native mixed-value reads
and mutations, nil input, and cross-module caller/provider round trips.
This design is not implemented or runtime-qualified.

The compile-only entry also reaches the affected module. A read-only static
audit of source `886fc03a71c7231b546debf0aa7d9bb5eaa48d32` found this chain of
plain imports (paths below `src/`):

`app/cli/bootstrap_main.spl:35` ->
`app/compiler_entrypoint/source_authority.spl:20` ->
`lib/scv/compile_snapshot.spl:33` -> `lib/scv/store.spl:16` ->
`lib/scv/shadow_write.spl:29` -> `lib/scv/stabilize.spl:11` ->
`lib/scv/journal.spl:19` -> `lib/scv/maintenance.spl:6` ->
`lib/common/compress/gzip.spl:8` ->
`lib/nogc_sync_mut/compression/gzip/compress.spl`.

The common gzip module also imports LZ77 at line 6. This is static module
reachability evidence, not a new execution result. With module-wide RTI
publication, the unchanged analysis declaration remains a blocker for that
closure as well as BuildRunner. The LZ77 repair alone does not unblock either
build. A function-level reachability solution would need an authoritative
export/provider policy; silently omitting this declaration is not a repair.

## Decoder dependency factoring

The common facade previously imported the monolithic `gzip.compress` module
only to reach its decoder. `gzip_decompress` now has a dedicated owner module;
the legacy `gzip.compress.gzip_decompress` entry forwards to that owner, and the
common facade imports the owner directly. The public API and decoder body,
including its optional-collection workaround, malformed-input behavior,
multi-member concatenation, trailer checks, and nil result, are preserved.
This factors the compile-only import edge but does not repair RTI publication:
the common facade still imports LZ77 for compression, and the unresolved
`gzip_analyze_data` declaration remains in `gzip.compress`.

Historical bootstrap success does not qualify the current pure-Simple native
producer. Historical source `2f55ac2a6d67` already had the same static import
chain. Attempt 17's `stage2-native-build.log` says at line 1 that the Rust seed
skipped unsupported `dynload` for one-binary emission, then reports 1,618
compiled, 0 reused, and 0 failed at line 11. Its later pure-Simple RTI failure
is consistent with that earlier seed-based success; no seed fallback or new
execution was performed for this factoring change.

The new decoder owner spec covers independent stored empty and `abc` members,
concatenation, malformed header, truncated body/trailer, CRC mismatch, legacy
wrapper parity, and common-facade roundtrip. It is authored but **UNRUN**. This
change does not resolve the separate old native untyped byte boxing issue and
does not qualify native behavior.
