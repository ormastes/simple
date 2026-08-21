# test/01_unit/compiler/driver — triage and backlog (2026-08-21)

## Method

The 579/487/92 figure quoted for this directory came from a whole-directory
run with no attribution. This record replaces it with a per-spec baseline:
every one of the 122 `*.spl` specs under `test/01_unit/compiler/driver` was run
individually with `bin/simple test <file>` and its `N examples, M failures`
lines summed. Per-spec logs make each failure attributable to a spec, an
example, and a message; the directory-level number does not.

**Baseline (per-spec, at 220695f76027 / 9ce4dc4f0a3):** 484 examples,
422 passed, **62 failed**, concentrated in 14 of 122 specs.

## Cluster table

| # | Cluster | Fails | Specs | Root cause | Class |
|---|---------|------:|-------|------------|-------|
| 1 | `dependency_interface_fold` missing | 7 | dep_interface_cache_key | The Phase D fold landed in `b8eeb9196f6` and was deleted by the stale-snapshot commit `bec01ea9587` ("seed (already broken) + docs"). `driver_build/incremental.spl` still imported and called it. | REGRESSION (clobber) |
| 2 | Brace interpolation in `to_contain` literals | 6 | leak_check_owner_imports, native_cache_granularity_contract, phase2_numeric_interpolation_ownership | `to_contain("... .{X}")` was parsed as string interpolation, so the spec died with `variable X not found` instead of comparing text. The tree's established escape is `\{ \}` (see function_local_use_discarded_spec). | STALE spec |
| 3 | Driver module split — file repoint | 7 | low_memory_source_fingerprint (1 ex, 5 anchors), compiler_driver_type_owner_contract (3) | `driver.spl` was split; the phase-order anchors moved verbatim and in order into `driver_orchestration.spl` (`ae55a746719`). Four further renames left contracts intact: `parse_source -> ParserModule`, `monomorphize_impl(hir_phase_admitted)`, `ctx.error_count() -> ctx.error_count_value`, `self.ctx.has_errors() -> ctx.has_errors()`. | STALE spec |
| 4 | Progress emit moved from stderr to stdout | 2 | non_tty_build_progress_flush_contract | `b4872f73454` deliberately replaced `eprint`+`stderr_flush` with a stdout twin + `rt_stdout_flush`, and turned the `if path != ""` wrapper into an early `if path == "": return` placed AFTER the emit. The invariant (emit+flush precede the optional-path check) is unchanged. | STALE spec, reviewed replacement |
| 5 | Flat parameter lowering + array type tags lost | 2 (partial) | bootstrap_post_entry_lowering_source | `b761623574a` ("lower flat function parameters") was dropped by the `6f86ff32a7d` wipe / `ae55a746719` restore, leaving `val param_count = 0` and `symbols.define("", SymbolKind.Parameter, ...)` — declared parameters were never lowered — and `TYPE_ARRAY_{I64,TEXT,BOOL,ANY}` fell through `bootstrap_hir_type_from_tag`. | REGRESSION (clobber) |
| 6 | Bootstrap/AOT source-text assertions after refactor | 32 | bootstrap_context_mir_source (12), native_build_cache_plumbing (9), bootstrap_mir_to_llvm_owner_mutation (7), native_build_jit_ambiguity (4) | Whitespace-exact source assertions against `80.driver`, `50.mir` and `70.backend` files that four concurrent lanes are actively splitting and renaming. Some anchors moved to a sibling module; some no longer exist in any form. Each needs a per-assertion "did the contract survive the refactor" judgement, not a mechanical repoint. | STALE spec + possible REAL, needs per-assertion review |
| 7 | `rt_string_free` reclamation | 3 | low_memory_source_fingerprint | `ctx.reclaim_source_contents()` returns 0 because `rt_string_free` does not report a freed heap string under the current Rust seed interpreter; it is implemented in the C runtime (`runtime_native.c:6382`). | ENV-dependent — needs a deployed native/self-hosted binary |
| 8 | VHDL design-catalog precondition | 3 | riscv_gen2_strict_source_route | All three examples get `VHDL design catalog found no @hardware entry in selected root module(s)` before reaching the assertion under test. | ENV-dependent / fixture gap |
| 9 | Streaming module surface lifecycle | 3 | streaming_module_surface_lifecycle | `unwrap()` on nil, and `Streaming module surfaces missing after phase 2`; the phase-2 streaming surface path does not produce surfaces in this harness. | REAL, open |
| 10 | Flat local-decl HIR lowering never implemented | 1 (partial) | bootstrap_post_entry_lowering_source | `HirStmtKind.Let(local_symbol, local_type, init_expr)` and its two siblings match **no commit in the entire history** — this half of the spec was written against a shape that was never built. | REAL old gap, aspirational spec |

## Fixed in this pass

| Cluster | Commit | Effect |
|---|---|---|
| 1 | (restored in tree; content verified identical to `b8eeb9196f6`) | dep_interface_cache_key 7 -> 0; sif_roundtrip and cache/persistent_code_cache green as neighbours |
| 2 | `d906f7f8798` | leak_check_owner_imports 2 -> 0, phase2_numeric_interpolation 2 -> 0, native_cache_granularity 2 -> 0 |
| 3, 4 | `ee059052ce4`, `fc15cc47973` | non_tty 2 -> 0, compiler_driver_type_owner 3 -> 0, low_memory 4 -> 3 |
| 5 | `fc15cc47973` | 7 of 9 assertions in bootstrap_post_entry_lowering now pass; flat parameters and array type tags lower again |

## Not fixed, and why

- **Cluster 6 (32 failures).** These specs pin exact source text in four files
  that other lanes are editing concurrently
  (`driver_source_pipeline_parsing.spl`, `driver_aot_native_output.spl`,
  `driver_source_loading.spl`, `native_build_worker.spl`). Repointing them
  mechanically would convert a real signal into a green light; several
  asserted strings exist in no form anywhere in `src/`, which means the
  contract itself may have been dropped rather than moved. Each needs the same
  archaeology clusters 1 and 5 got.
- **Clusters 7 and 8 (6 failures).** ENV-dependent. `test/01_unit/compiler/driver`
  has **no** skip/pending/xit mechanism in use — grepping the directory returns
  zero occurrences — so no assertion was weakened, skipped, or deleted to make
  these pass. They are recorded here instead.
- **Clusters 9 and 10 (4 failures).** Real open gaps, out of this lane's scope.

## Two clobbers, one mechanism

Clusters 1 and 5 are the same failure mode twice: a whole-working-copy snapshot
commit (`bec01ea9587`, `6f86ff32a7d`) silently reverted landed work, and no
pre-push guard saw it, because the tree stayed structurally valid. Both losses
were found only because a spec asserted the missing code by name. That is an
argument for keeping symbol-level source assertions, and against repointing
them without reading what moved.

## Before / after (per-spec, sharded, whole directory)

| | examples | passed | failed | specs with failures |
|---|---:|---:|---:|---:|
| before | 484 | 422 | 62 | 14 of 122 |
| after  | 481 | 441 | **40** | 7 of 122 |

Remaining 40, by spec: bootstrap_context_mir_source 12,
native_build_cache_plumbing 9, bootstrap_mir_to_llvm_owner_mutation 7,
native_build_jit_ambiguity 4 (all cluster 6); riscv_gen2_strict_source_route 3
(cluster 8); low_memory_source_fingerprint 3 (cluster 7);
bootstrap_post_entry_lowering 2 (clusters 5 and 10 residue).
`streaming_module_surface_lifecycle` (cluster 9) is green in the after run.

The example count differs by 3 between runs because several of these specs
abort mid-file on the first failing assertion, so the number of examples that
get to report at all moves with what is passing.
