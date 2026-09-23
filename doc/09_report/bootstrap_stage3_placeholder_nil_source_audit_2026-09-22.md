# Stage 3 module-surface nil failure: source audit

Date: 2026-09-22. Audited main: `e0dd873da1b7828389db4eb60e82972cc8245313`.
Bug: `bootstrap_stage3_module_surface_placeholder_nil_2026-08-01`.

## Result

Source fix already present; tracking reconciliation only. No compiler, runtime,
test, or build configuration changes are introduced by this change.

`f7b1e508e892ad99a3a13c8e556926b69ec56406` (authored 2026-08-01,
`fix: advance stage4 bootstrap HIR recovery`) introduced the fix and is an
ancestor of audited main (`git merge-base --is-ancestor` returned 0).
The bug document gained its closed heading in the September ledger cleanup,
but its Status paragraph, recent list and worklist descriptions remained stale.
The database row already had status `fixed`.

## Exact failure and adjacent source controls

The original admitted Stage 2 produced a nil receiver trap while Stage 3 built
module surfaces, at source index 6 of 800. The recorded investigation isolated
an incorrect `Dict<text, i64>` bracket lookup in the physical-path parse cache.

The fixing diff and current `src/compiler/80.driver/driver_source_pipeline_parsing.spl`
retain these properties:

- Scalar parallel key/index arrays use capacity `2 * unique_sources + 1`, so
  insertion cannot fill the table under the unique-source precondition.
- Insertion and lookup use the same `_driver_text_bucket_index` and linear
  probing, wrapping with modulo capacity. This handles colliding physical keys.
- Missing keys fail with a parse-cache diagnostic before any payload indexing.
- `ParsedEntryModuleBox` handles retain parsed modules; an absent box fails
  before `.value` is consumed.
- The current poison path intentionally skips a missing poisoned source while
  retaining its parse diagnostic; an unexpected missing source still fails.
- Surface aliases refer to physical modules; returned source rows are unique.

These are source observations, not newly executed behavioral tests. Existing
adjacent coverage includes
`test/02_integration/compiler/streaming_surface_builder_reference_stress_probe.spl`
(200 physical modules, 200 aliases and conflicting-content rejection) and
`test/unit/compiler/hir/module_surface_index_allocation_guard_spec.spl`.
Neither substitutes for the original staged-native reproduction.

## Evidence scope and host/backend matrix

| Lane | Evidence | Status |
| --- | --- | --- |
| Historical Linux x86_64 staged-native Stage 3 | Bug report records no nil trap, missing box or missing module; it then reached 135 separate HIR diagnostics | Recorded historical boundary pass; original build logs not available in this checkout |
| Current main source vs original fix | Ancestor check and fixing diff; current open addressing and boxed module ownership | Source-fixed confirmed |
| Windows x86_64 deployed interpreter/native codegen | Deployed `bin/release/x86_64-pc-windows-msvc/simple.exe --version` identifies itself as a Rust bootstrap seed | Not used: bootstrap-only binary |
| Windows x86_64 admitted Stage 2 | Candidate and receipt hashes verified; compiled driver source differs from audited main | Valid Stage 2 authority, not current-main driver execution evidence |
| Linux x86_64 in WSL | Ubuntu-22.04 is available; no admitted self-hosted runtime supplied for this lane | Not executed |
| ARM64, macOS/FreeBSD, alternative backend and CPU targets | No target execution or admitted compiler evidence available | Not executed |

The executable identification command printed `Simple Language v1.0.0-rc.1`
and the explicit warning that the Rust-built binary is bootstrap-only. It was
not used to execute tests. Repository rules prohibit falling back to that seed.

A separate pure-Simple Stage 2 was subsequently located at
`D:/simple_build/bootstrap-msvc/stage2/x86_64-pc-windows-msvc/simple.exe`, SHA-256
`4a8dd3eb3887b9cb61608dd6cc668dafa18bbd75bd0d98326328df48c6d54db5`.
Its provenance and sanity receipts reference the admitted Stage 2 receipt with
SHA-256 `70845f9d5b620aba245ed3e549881e79b5c7bc388c91f0e90562cf274a885310`.
That receipt says `status=admitted`; the candidate, source snapshot, runtime
snapshot, tool authority, sanity evidence and receiver evidence files all
matched the receipt hashes. The sanity/receiver evidence reports pass.

The source snapshot uses hex-encoded paths. Decoding the two relevant entries
shows that the admitted compiler is not built from this audited driver's source:

| Source | Admitted snapshot SHA-256 | Audited main SHA-256 |
| --- | --- | --- |
| `driver_source_pipeline_parsing.spl` | `631836f6b0c38a3805df40d764914f1cb9eb5cc08eb4061dfe101b0daa78fb55` | `4e550b165f78a0777a03e691d829f4edd0440998060c4f840dee47e30ae1ccde` |
| `driver_source_loading.spl` | `273a4905569c6ca523187b28a5616b5a40d4658a6f882cfe4299de523e8bdff8` | `760e4305c6fcb8bdf28211e55e5a938f5068189a39b7542f6c7cc14bd71c9718` |

This authority could bootstrap a fresh candidate, but a broad rebuild was not
performed for this source-fixed tracking reconciliation. Running the older
driver alone would not establish current-main driver behavior.

## Performance and memory

There is no production delta to benchmark against audited main. Compiler and
runtime source content is unchanged, so this tracking change introduces no
executable performance or memory change. Fresh Stage 3 elapsed time and peak
RSS were not measured; no cross-host, cross-CPU, backend, speed or memory
nonregression result is claimed. Historical progress past the original trap is
not a substitute for a current performance baseline.

## Completion boundary

Tracking validation passed: the canonical bug-status consistency script checked
this bug document against a copy of the full updated database in an isolated
fixture root (`PASS — 1 doc(s) checked, 0 disagreement(s)`). The canonical SDN
resealer passed its four fixtures and sealed the rebased database with CRC-32
`838090618`. The executable-spec count under `doc/06_spec` was zero.

The original bug is source-fixed; full Stage 3/4 acceptance and fresh runtime
revalidation remain outside this evidence. Reopen this bug only with a dated
reproduction of its original physical-cache/module-surface nil failure. Keep
later HIR semantic diagnostics and Stage 4 admission failures in their own
records. No duplicate implementation PR is needed.
