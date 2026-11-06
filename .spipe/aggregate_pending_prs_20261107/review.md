# Aggregate pending PRs, 2026-11-07

This branch integrates the 28 pinned inputs in inputs.sdn. Original PRs must remain open until this aggregate merges and their then-current heads are confirmed included.

## Integration mapping

- Broad lane: 9dbdc75521b45a795be8868b7fb91c7d610ab81d. See ../aggregate_broad_lane_20261107/mapping.sdn and integration-review.md. PR #7237 is patch-equivalent to two commits of #7265 and is not duplicated.
- Runtime lane: f5595872ca2e2c9756806de507bb33b98700ca4c. See runtime-mapping.sdn and runtime-decisions.md here.
- Compiler lane: abf97837ae005725bea6090d073dfd4156982ce7. See ../aggregate_compiler_lane_20261107/mapping.md.
- #7305: 04c3470126023edd7ef19c0e89576dff5dce812a -> 98d1ff534fc.
- #7319: 41fb5530ad3d49924f560a86abe29544a42cb4f5 -> 591fe872c8c.
- #7321: 9d835218572 -> c6975d18996; f7db7c3012e -> 325c985b9c9; 04f2b23aeb8 -> 552241bf2a3.

Conflict resolutions preserve released parser diagnostics, codec fields, runtime source lists, float guards and caller semantics. The combined flat-pool schema is v15 because both prior incompatible proposals used v14. These source integrations are not runtime qualification.

## Additional integration repairs and evidence

The baremetal boolean checker is now wired into runtime-file-copy-mode CI with relevant path triggers. `CC=clang sh scripts/check/check-baremetal-runtime-bool.shs` passed on this aggregate: seven constant owners and two real logical/conversion/predicate owners. This is C-only evidence.

The merged bug database was resealed through scripts/check/reseal-sdn-crc32.shs using native xxhsum. Eight hash fixtures passed; canonical seal is xxh3_69c0f53426b1b83a. Duplicate parent seals were removed by the canonical tool.

## Admission: BLOCKED

- #7294: recorded runtime SIGSEGV (139), zero assertions, exhausted repair budget. Aggregation does not resolve it.
- #7337: actual Simple consumer exit 14 at the saved transient-word-count assertion after result consumption and scope teardown. See runtime-process-capture-failure-audit.md. Failed fixture and relevant owners remain unchanged; no qualified passing replacement evidence.
- Required compiler/lib/MCP/LSP checks, MCP stdio and native smoke, parser and MIR regression specs, Windows/MSVC integration and source-matched runtime qualification remain incomplete.
- Compiler-only bootstrap attempt 7 completed HIR for 1600 modules but failed seven codegen shards; no compiler output, no Hello execution. No further bootstrap attempt was authorized.

Do not represent narrow native checks or static hooks as full verification PASS. No original PR may be closed on the strength of this draft alone. Release tags/publication are outside scope.

## Publication synchronization

Merged live release target 53f7d4948b436092b543d95c32db7d756a455766 (three archive source-exclusion changes) without conflicts. The initial push incorrectly selected main as its range base; the six reported runtime-symbol removals are absent already on the pinned release base, and none are removed by this aggregate. Configured the owned branch upstream to release/1.0.0 so the normal hook queries and checks the intended live release authority. No hook was bypassed. Runtime admission remains blocked.
