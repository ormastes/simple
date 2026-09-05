# MIR / Codegen Optimization Audit — 2026-08-23

Lane: OPTIMIZATION. Scope `src/compiler/50.mir/**`, `60.mir_opt/**`, `70.backend/**`.
Method: static enumeration + **end-to-end `native-build --entry-closure` runs** on a
loop fixture, in a clean worktree at `origin/main` `504a57d11c8` (`/mnt/fast/wt-miropt-1`).

## 0. Environment note (blocking, not mine to fix)

The *shared* worktree `/mnt/data/worktrees/simple-main` is broken by an **uncommitted**
edit from another lane: `src/compiler/20.hir/hir_types.spl:212` declares
`fun qualified_symbol_key(...)` where HEAD has `fn`. Every `native-build` and
`bin/simple test` in that tree dies with `error[E1002]: function \`fun\` not found`.
Not present at `origin/main`. All measurements below were therefore taken in a clean
worktree. **Not touched** (another session's working copy).

## 1. Is the pipeline wired? YES — measured, not inferred

`SIMPLE_COMPILER_TRACE=1` emits `[mir-opt] pass:start/done`. Fixture: 12-line loop with
a loop-invariant expression, a dead store, an unused local, a foldable constant.

| invocation | `pass:start` count | binary bytes | output |
|---|---|---|---|
| `--opt-level 0` | **0** | 42,960 | 645 ✓ |
| default (no flag) | 48 (16 passes × 3) | 27,744 | 645 ✓ |
| `--opt-level 2` | 48 (16 × 3) | 27,440 | 645 ✓ |
| `--release` | **32 (16 × 2)** | 27,744 | 645 ✓ |

**Measured effect: −36% object size at O2 vs O0, output identical.** The pipeline is
real, effective, and correct on this fixture. This is the first end-to-end evidence of
steps 4/6–6/6 producing a working binary from the pure-Simple driver.

Note `-O2` is **not** a `native-build` flag (`Error: unknown option: -O2`); the flags are
`--opt-level <n>` and `--release`.

## 2. Pass table

Pipelines enumerated by executing `optimizationpipeline_passes_for_backend`
(probe run, not read off source): Size 9, Speed 20, Aggressive 24 passes;
after LLVM-backend filtering **Speed/llvm 16 and Aggressive/llvm 16** — i.e.
**`--release` (Aggressive) buys literally nothing over `-O2` on the default LLVM
backend.** Native backend keeps all 20.

| pass | wired | fires (evidence) | notes |
|---|---|---|---|
| dead_code_elimination | ✅ ×2/pipeline | ✅ trace + spec | |
| constant_folding | ✅ ×2 | ✅ trace + `constant_folding_spec` | |
| copy_propagation | ✅ | ✅ trace + spec | |
| global_value_numbering | ✅ | **skipped on llvm** (`llvm_runs_gvn…`) | **no unit spec exists** |
| common_subexpr_elim | ✅ | **skipped on llvm** | **no unit spec exists** |
| inline_{small,functions,aggressive} | ✅ | **skipped on llvm**; also skipped under `SIMPLE_BOOTSTRAP=1` (`mir_opt_bootstrap_skip_pass`) | inlining is off in every bootstrap stage |
| loop_invariant_motion | ✅ | ✅ trace + `loop_invariant_motion_spec` (9 ✓) | dispatches to `loop_opt` conservative, **not** `loop_licm.spl` |
| loop_unroll / strength_reduction | ✅ (Aggressive only) | **skipped on llvm** | |
| bounds_check_elimination | ✅ | ✅ trace + spec (7 ✓) | |
| tail_call_optimization | ✅ | ✅ trace | |
| generator_state_machine | ✅ | ✅ trace | |
| body_outlining | ✅ | ✅ trace | |
| collection_opt / string_builder_opt | ✅ | ✅ trace + `collection_opt_spec` (31 ✓) | skipped under bootstrap |
| pattern_idiom | ✅ | ✅ trace; **no-op unless rules supplied** by DynamicPassRegistry | |
| target_narrow_form | ✅ | ✅ trace; no-op via bare `run_pass_on_module` | |
| write_coalesce / syscall_batch | ✅ | ✅ trace | `read_ahead_hoist` in registry but **in no pipeline** |
| auto_vectorize | ✅ | **skipped on llvm**; spec 57/64 (7 ✗) | mod.spl comment "no MIR rewrite in Wave K3" is **stale** — `_AutoVectorize/rewrite.spl` does rewrite |
| predicate_promote | ✅ (Aggressive) | **skipped on llvm**, skipped under bootstrap | |
| typed_byte_canon | ✅ registry | **in no pipeline list** | implemented, spec-green (10 ✓), never scheduled |

### Implemented but UNWIRED (zero call sites anywhere in `src/` or `test/`)
- `60.mir_opt/mir_opt/bitmanip_lowering.spl` (274 lines) — **no reference at all**.
- `60.mir_opt/mir_opt/masked_simd_op.spl` (87 lines) — **no reference at all**.
- `simd_lowering.spl::run_simd_lowering` — exported + named in `optimizer_manifest`, but in **no pipeline pass list**.
- `loop_licm.spl` (280 lines) — only consumer is a type import in `loop_opt.spl`; LICM dispatch uses `loop_opt` instead.
- `read_ahead_hoist`, `typed_byte_canon` — registry entries, never scheduled.

Same defect class as `interface_digest_of` / `smf_manifest_entry_verifies`.

## 3. Cost (`SIMPLE_BUILD_PROGRESS_EVENTS=1`, hello fixture)

| step | O2 | O0 |
|---|---|---|
| 1/6 parse | 3,408 ms | ~2,000 ms |
| 4/6 mir (incl. all MIR opt) | **383 ms** | (n/a) |
| 5/6 native_compile | 486 ms | 543 ms |
| **6/6 link** | **56,544 ms (93%)** | 15,044 ms |

**MIR optimization is not the cost — linking is.** MIR+codegen together are <1s;
link is 15–57 s for a hello world. Any effort spent making passes cheaper is
misallocated until the link step is addressed.

**Redundant work found:** the full pipeline runs **3×** per default build and **2×**
under `--release` over the same modules — `CompilerDriver.optimize_mir_level`
(`80.driver/driver_pipeline_passes.spl:31`), then `optimize_module_for_backend`
(`70.backend/backend/backend_helpers.spl:461`), then
`optimize_module_with_context` (`70.backend/backend/llvm_backend.spl:243,268`).
Cheap on hello-world; triples MIR-opt cost on a real tree.

## 4. Ranked improvements

1. **Dedupe the 2–3× pipeline re-run** (driver vs backend_helpers vs llvm_backend).
   Value: high on large builds. Risk: medium — passes are idempotent today, so the
   removal must be proven by output-identity on a fixture set before landing.
2. **`Aggressive` == `Speed` on the LLVM backend (both 16 passes).** `--release` is
   a no-op relative to `-O2` today. Either state that in `--help` or move
   `loop_unroll`/`strength_reduction`/`gvn` out of the LLVM skip list. Risk: low (docs) / medium (skip list).
3. **Add unit specs for GVN and CSE** — the two passes with zero spec coverage that
   sit in every non-LLVM pipeline. Risk: none.
4. **Schedule or delete `typed_byte_canon` and `read_ahead_hoist`** — implemented,
   spec-green, never run. Risk: low.
5. **Delete or wire `bitmanip_lowering.spl` + `masked_simd_op.spl`** (361 dead lines).
   Wiring needs a design decision (target gating) — file, don't improvise.
6. **Fix the stale `auto_vectorize` comment** in `mod.spl` and the 7 failing
   `auto_vectorize_spec` cases. Risk: low.
7. **`pipeline_optimize` is O(passes × functions) with a fresh pass object per
   function per pass** — 16 passes × N functions allocations. Only worth touching
   after (1), given the link-dominated profile.

## 5. Not implemented (for completeness)
No sinking/partial-redundancy elimination, no scalar replacement of aggregates,
no interprocedural constant propagation, no profile-guided layout. Not defects —
the LLVM backend covers most of these; they matter only for the custom native backend.
