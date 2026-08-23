# Phase-1 Scoped Test Suite — Measured State (2026-08-23)

Tree: `origin/main` @ `b5f8e6ac557`, private worktree `/mnt/fast/wt/phase1tests-1`.
Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 60,650,360 bytes, mtime
2026-08-23 04:47:05 — the seed deployed at `f421d425e34`.

> **Caveat, stated up front:** this is the **Rust seed**, not the pure-Simple
> self-hosted binary. run25 (the sole phase-1 build) still owns that lane, so no
> self-hosted binary was available to measure against. Every number below is a
> seed measurement. Per `.claude/rules/bootstrap.md` the designated tool is the
> self-hosted binary, so this sweep must be repeated once run25 lands.

## 1. Scope decision (a deliverable in its own right)

Phase 1's gate is "the whole set of Simple compiler / interpreter / loader
related tests", not the whole tree.

**Included — 2,179 specs of 21,228 tree-wide (10.3%):**

| Path | Specs | Why |
|---|---:|---|
| `test/01_unit/compiler/**` | 2,063 | the compiler proper |
| `test/02_integration/compiler/**` | 43 | end-to-end driver/codegen |
| `test/01_unit/app/cli/` | 69 | drives the driver/loader entry path |
| `test/01_unit/app/compile/` | 4 | compile-command surface |

**Excluded deliberately:**

- `test/01_unit/bugs/`, `test/fixtures/`, `test/tmp_repro/` — red by
  construction; counting them would fabricate failures.
- ui, browser, os, ml, gpu, scilib, net, db and the rest of the tree — not on
  the compiler/interpreter/loader path. No claim is made about them here.

Verified the exclusions are genuinely absent from the scope list (0 matches).

## 2. Counts — all measured, none inferred

| Outcome | Specs |
|---|---:|
| **In scope** | **2,179** |
| **Executed** | **2,179 (100%)** |
| Passed | 1,763 |
| Failed | 412 |
| Hung (600s SIGKILL) | 4 |
| Unmeasured / externally killed | **0** |
| Aborted with no `Results:` line | **0** |

Example-level, across specs that produced a `Results:` line:
**16,528 examples — 15,531 passed, 997 failed.**

Pass rate: **80.9% of specs**, **94.0% of examples**.

No run was counted without a `Results:` line, no exit code was read through a
pipe, and every spec was passed as an explicit file path (never a directory), so
the `@cover` preflight trap is structurally unreachable here. `--no-cover-check
--no-self-protect` were used throughout; `SIMPLE_TIMEOUT_SECONDS=0`.

Zero SIGTERM kills were observed, so the earlyoom-victim hazard did not perturb
this measurement.

### Hung specs (4)

- `test/01_unit/compiler/50.mir/hwir_zca_target_trap_exhaustive_oracle_spec.spl`
- `test/01_unit/compiler/driver_provider_v1_spec.spl`
- `test/02_integration/compiler/driver/native_build_frontend_cache_second_build_hits_spec.spl`
- `test/02_integration/compiler/driver/native_build_parse_sharding_spec.spl`

These exceeded 600s wall. They are reported as HUNG, not as failures — no
verdict was produced for them.

## 3. Failing set by root cause

994 of 997 failing examples were mechanically attributed by parsing each
failing example's `✗` line and its reason line.

| Root cause | Examples | Specs |
|---|---:|---:|
| VALUE_MISMATCH | 344 | 174 |
| SEMANTIC_ERROR | 236 | 99 |
| **RENAME_MOVE_DRIFT** | **222** | **118** |
| MISSING_SYMBOL | 61 | 27 |
| UNIMPLEMENTED_FEATURE | 24 | 14 |
| PATH_NOT_FOUND | 2 | 2 |
| OTHER (unattributed) | 90 | 64 |

### RENAME_MOVE_DRIFT — confirmed dominant structural class (118 specs)

As predicted. These specs assert on **source text** — a file's banner comment or
its `use` lines — and the assertion drifted when the file was renamed, moved, or
split. Representative reasons:

- `expected # Part N of src/compiler/40.backend/backend/mir_to_llvm.spl` (18)
- `expected # HIR item lowering - module, import, and bootstrap-flat lowering` (27)
- `expected # HIR expression lowering umbrella.` (12)
- `expected use compiler.driver.driver_compiler_type.{CompilerDriver}` (7)
- `expected use compiler.hir.hir_types.*` (4)

This class is mechanical to repair and carries no product risk — but it is also
the reason the suite's red is not a reliable signal today.

### Per-area distribution of failing specs

| Area | Specs | Failed | Hung |
|---|---:|---:|---:|
| compiler/hir | 132 | 52 | 0 |
| compiler/backend | 211 | 48 | 0 |
| compiler/codegen | 94 | 37 | 0 |
| compiler/driver | 130 | 32 | 0 |
| compiler/bootstrap | 57 | 30 | 0 |
| compiler/mir | 96 | 30 | 0 |
| compiler/interpreter | 86 | 21 | 0 |
| app/cli | 69 | 13 | 0 |
| compiler/frontend | 81 | 12 | 0 |
| compiler/linker | 48 | 12 | 0 |
| compiler/parser | 97 | 12 | 0 |
| compiler/verification | 25 | 12 | 0 |
| compiler/loader | 37 | 9 | 0 |
| compiler/50.mir | 27 | 7 | 1 |
| compiler/semantics | 81 | 5 | 0 |

## 4. Pre-existing vs. caused by today's landed fixes

Touch-correlation is **not** usable evidence here: `origin/main` took **573
commits in the last 24h** touching 10,043 `.spl` files, far more churn than the
"~20 landed fixes" framing.

So this was measured directly. A 32-spec stratified sample (up to 5 failing
specs per root-cause class) was re-run **with the same binary** against a
24h-old tree (`a32c3f3464fa`, 2026-08-22 06:29).

| Result on the old tree | Count |
|---|---:|
| **FAIL_IN_OLD — pre-existing** | **25** |
| PASSED_IN_OLD — candidate regression | 2 |
| ABSENT_IN_OLD — spec is new | 1 |
| did not complete in the window | 4 |

**Conclusion: ~89% of sampled failures are pre-existing.** The phase-1 red is a
standing backlog, not damage from today's changes.

### The 2 candidate regressions — and they are not what the bucket label says

- `test/01_unit/compiler/backend/c_backend_async_spec.spl`
- `test/01_unit/compiler/backend/backend_capability_spec.spl`

Both were auto-bucketed UNIMPLEMENTED_FEATURE, and that classification is
**wrong on inspection**. Their example names are:

- "emits explicit panic code for CreatePromise"
- "names the backend and unsupported async operation in C lowering"
- "names the backend and unsupported matrix operation in LLVM lowering"

The specs *assert that the compiler emits a clean, named diagnostic* for an
unsupported operation. What happens today is `semantic: panic: compile error: C
backend does not support async CreatePromise lowering` — the condition escapes
as a **hard compile panic** instead of the structured diagnostic the spec
requires. The unsupported-op handling is the feature under test; it regressed in
the last 24h. This is a real error-reporting regression and should be treated as
such, not filed as a missing backend feature.

## 5. Genuinely unimplemented optional features (TODO candidates)

Per the standing policy — record incomplete-and-optional work as a TODO, do not
fix it opportunistically, and do not skip anything in source (CLAUDE.md forbids
skipping failing tests without approval, so **nothing was disabled or ignored by
this sweep**).

One finding is more valuable than the per-spec list: the reason
`semantic: invalid assignment: complex indexed field receiver is not supported`
appears in **6 unrelated specs** across `50.mir`, `backend`, `hir`, `mir`, and
`verification`. That is a **single seed-compiler gap**, not six spec defects —
`a[i].b = v` style assignment through a complex indexed receiver. Fixing that one
gap should clear all six.

Remaining genuine backend gaps, by asserted capability:

| Gap | Specs |
|---|---|
| LLVM: MatMul / Transpose / SIMD `vec_sum` lowering | `backend/llvm_matrix_lowering_spec.spl`, `backend/backend_capability_spec.spl` |
| C backend: async CreatePromise / Await / Spawn, actor Receive | `backend/c_backend_async_spec.spl`, `backend/backend_capability_spec.spl` |
| VHDL: Unit local signal, artifact manifest | `backend/vhdl_backend_spec.spl`, `backend/vhdl_clocked_global_state_contract_spec.spl`, `backend/vhdl_artifact_manifest_spec.spl` |
| OpenCL backend contract | `codegen/opencl_backend_contract_spec.spl` |
| HWIR: strict combinational `xor` | `50.mir/hwir_riscv_scalar_trap_projection_spec.spl` |
| Loader: cast to `Pointer{Shared, u8}` | `loader/native_mmap_byte_read_spec.spl` |

(Note the overlap with §4: the two async/capability specs are listed here for
their *other* examples, but their headline failures are the regression above.)

## 6. What could not be measured

- **The self-hosted binary.** Everything here is the Rust seed. run25 owns the
  pure-Simple build; the sweep must be repeated against it.
- **4 hung specs** produced no verdict at 600s. Whether they are slow or
  genuinely deadlocked is unresolved.
- **90 failing examples (64 specs)** did not match any attribution rule and are
  reported honestly as OTHER rather than forced into a bucket.
- **4 of 32** old-tree comparison runs did not finish inside the window, so the
  pre-existing ratio rests on 28 completed comparisons, not 32.
- The pre-existing/regression split is a **stratified sample**, not a full
  re-run of all 412 failures against the old tree.
- `E1002 runtime_file_rename` was **not observed** in any run.

## 7. Method

- 8 concurrent workers max, with a back-off loop pausing new work while
  1-minute load exceeded 28; run25 was never competed with for a `native-build`.
- Every spec invoked by **explicit file path**.
- Exit status read directly into a variable on the line after the invocation,
  never through a pipe.
- A run with no `Results:` line would have been recorded ABORTED/UNKNOWN; none
  occurred.
- rc 137/124 → HUNG; rc 143 or other rc ≥ 128 → UNMEASURED (external kill),
  never a failure.
- Raw per-spec logs and TSVs retained in the session scratchpad.
