# In-Development Tag Sweep — integration slice (`test/02_integration`, `test/integration`, `test/feature`)

**Date:** 2026-08-23
**Slice:** 3 of 4. Sibling lanes cover unit, system, and perf/other.
**Tag under sweep:** `# @tag:in-development` (`src/lib/nogc_sync_mut/spec/in_development.spl`, landed `970920e02cd`).
**Worktree:** `/mnt/fast/wt-tagsweep-integration` at `origin/main` `21fb80be31e`.
**Binary:** deployed `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed; the tree's only working binary).

## Headline

**Zero specs tagged.** Every failure classified so far is a *real defect*, an
*environmental* gap, or *harness debt* — none of them is unfinished feature work,
which is the only thing the tag is allowed to mean. The left-red list below is
this slice's product.

## Method

- Per-file runs, never directory runs (a directory run corrupts the shared DB per
  `.claude/rules/testing.md`). `SIMPLE_TIMEOUT_SECONDS=0`, `timeout 200`,
  `--timeout 150`, `--no-cover-check`.
- Verdict is the last `Results:` line **plus** a non-vacuity check: a log with no
  `PASS`/`FAIL` and no `SPEC FILE VERDICT` line is classified `NO-EXEC`, never PASS.
  Exit status is read into a variable directly, never through a pipe.
- **`@cover` preflight-gate audit (coordinator advisory).** All batches run before
  `--no-cover-check` was added were re-audited for the gate's tells (`Time: 0ms`,
  `AFTER_RUN_0_files`, zero verdict lines, `rc=3`). **No log showed them** — every
  recorded FAIL carried both a `SPEC FILE VERDICT` and a `PASS`/`FAIL` line, so no
  result in this report is gate contamination. `--no-cover-check` is in force from
  the single-job restart onward regardless.
- **Resource-watchdog truncation audit (coordinator advisory #2).** The runner's
  self-protection watchdog (`test_runner_main.spl:369,412`, `resource_limit_pct` 75,
  sampled system-wide every 20 tests) exits **42** with `GRACEFUL SHUTDOWN` and a
  plausible-looking partial summary, so a sweep that trusts it measures only the
  first ~20 specs per invocation. Audited across every log and result row in this
  slice: **0 rows with `rc=42`, 0 logs containing `GRACEFUL SHUTDOWN`** — the
  observed exit codes are only 0 and 1. One-spec-per-invocation batching is what
  makes this slice structurally resistant to that gate: the 20-test sampling
  boundary is rarely reached inside a single spec file, and a truncation would in
  any case be caught by the per-file `SPEC FILE VERDICT` non-vacuity check above.
  `--no-self-protect` is added alongside `--no-cover-check` for the remainder.
- **Three independent ways this tree reports things that did not happen** are now
  known, and this slice is checked against all three: the incoherent recorded DB
  (`Total 770 / Passed 0 / Failed 0` — not used here at all), the `@cover` phantom
  failures, and the watchdog truncation. The counts below survive all three checks.
- **Explicit paths, never a directory.** Every invocation in this slice names one
  spec file. A sibling lane established that the `@cover` preflight lives in the
  runner's *discovery* mode, so explicit paths make gate 1 structurally unreachable
  rather than merely flagged off — which is the independent reason the audit above
  came back clean. It also means a future `ABORTED BEFORE EXECUTION` block (landed
  as `af3c30ecdaa`, not yet in the deployed seed) cannot silently supply counts
  here; on this binary the operative tells remain `Time: 0ms`,
  `AFTER_RUN_0_files`, absent `PASS`/`FAIL`, `rc=3`, and `rc=42`.
- **Mirror handling.** `test/integration/` is a *strict subset* mirror of
  `test/02_integration/`: 592 common paths, 184 unique to `02_integration`, **0
  unique to `integration`**. Running both would duplicate 592 executions for no
  information, so only `test/02_integration` + `test/feature` (1128 specs) are
  executed and any tag would be applied to both twins together, satisfying
  `scripts/check/check-test-tree-divergence.shs`.

## Throughput — why coverage is partial

The box is shared with three sibling sweep lanes; load average measured 33–36
throughout. Effective throughput was **~0.5 spec/min at 2 jobs**, and the lane was
cut to **1 job** mid-run on the coordinator's memory-pressure instruction. A full
1128-spec sweep is a ~20–30 hour job at that rate. Coverage is reported honestly
rather than extrapolated.

## Left red — and why (the valuable output)

| Spec | Failure | Class | Why not tagged |
|---|---|---|---|
| `test/feature/lib/gc_parity/gc_module_loader_spec.spl` | `does not expose an unimplemented gc_sync_mut family` — expected true to equal false | **architectural regression** | `src/lib/gc_sync_mut/` **exists in the tree**. The spec asserts the no-GC-first direction is not reversed by a stub family, and it is correct: the directory is there. This is a defect to remove, not a feature to finish. |
| `test/feature/scilib/linalg_simd_spec.spl` | `runtime: rt_simd_mul_f32x4: field x must be a float, got Float32(1.0)` | **runtime type-dispatch defect** | The runtime rejects its own `Float32` as "not a float". That is a wrong-behaviour bug in `rt_simd_mul_f32x4`, not a missing capability. Deserves a bug record. |
| `test/feature/scilib/ndarray_broadcast_spec.spl` | same `rt_simd_mul_f32x4` runtime error across every F32 lane case | **same defect** | Same root cause as above. |
| `test/feature/scilib/cuda_device_buffer_spec.spl` | `round-trips host i64 values through a device buffer when CUDA is available` | **defect on a live capability** | The spec is availability-gated and takes the `cuda_available()` branch, i.e. CUDA *is* reported present (this host has two NVIDIA GPUs). The transfer path then fails. A gated spec that fails inside its available-branch is a broken implementation, not an unimplemented one. |
| `test/feature/scilib/linalg_torch_backend_spec.spl` | PyTorch-owned tensor creation/reshape/permute all fail | **defect on a live capability** | Same shape: the spec explicitly accepts `Err(BackendError.BackendUnavailable)` as a pass. It is not taking that branch, so the shim reports itself available and then misbehaves. |
| `test/feature/scilib/df_missing_values_spec.spl` | `expected Float64(value: 0.0) to equal Float64(value: 3.0)`, `Index(3)` vs `Index(2)` | **wrong results** | Drop-missing computes the wrong values and the wrong row count. Silent wrong answers, not absent answers. |
| `test/feature/scilib/df_filter_spec.spl` | `filters rows and preserves Float64 and Int64 column dtypes` | **wrong results** | Same class. |
| `test/feature/scilib/ndarray_index_spec.spl` | mask-compaction returns wrong element and wrong length | **wrong results** | Same class. |
| `test/feature/scilib/ndarray_concat_stack_spec.spl` | `returns UnsupportedDType for Bool stack in this 1-D v1 slice` — expected false to equal true | **wrong error contract** | The v1 slice is documented as deliberately 1-D, and the spec asserts the *typed rejection* that scope requires. Failing to reject is a contract defect, not unfinished scope. |
| `test/feature/usage/arithmetic_spec.spl` | `handles deeply nested parentheses` — **expected 8 to equal 6** | **wrong arithmetic result** | The compiler evaluates a nested-parenthesis expression to the wrong number. A wrong answer from integer arithmetic is the most serious class of defect in this list; it is emphatically not an unfinished feature. |
| `test/feature/usage/classes_spec.spl` | `dispatches method to context object`, `accesses self fields in context method` — expected 0 to equal 42 | **wrong dispatch** | Method dispatch and `self` field access on a context object silently return 0. Silent zero, not an error. |
| `test/feature/usage/actor_model_spec.spl` | `semantic: method `Vec3` not found on type `dict` (receiver value: {MATH_E: ..., MATH_INF: ...})` | **name-resolution defect** | A constructor call resolves its receiver to the *math module's constant dict* instead of the type. A misresolution, not a missing capability. |
| `test/feature/usage/aop_spec.spl` | `executes before advice before target`, `executes after_success when target succeeds` | **AOP advice not firing** | Advice is declared and matched but does not run. |
| `test/feature/usage/aop_pointcut_spec.spl` | `matches exact function name`, `matches any return type with wildcard` | **pointcut matching defect** | Even an exact-name pointcut fails to match. |
| `test/feature/usage/advanced_indexing_spec.spl` | `handles UTF-8 characters` — expected `\ufffd` to equal `\U0001f30d` | **byte-vs-codepoint indexing defect** | Indexing splits a multi-byte codepoint and yields a replacement character. |
| `test/feature/scilib/ndarray_simd_spec.spl`, `ndarray_ufunc_spec.spl`, `ndarray_reduction_spec.spl`, `simd_f32_spec.spl` | `rt_simd_add_f32x4` / `mul_f32x4` / `sub_f32x4` / `fma_f32x8`: `field x must be a float, got Float32(...)` | **same runtime type-dispatch defect** | One root cause shared with `linalg_simd` and `ndarray_broadcast`: **six specs, one bug**. The SIMD runtime entry points reject their own `Float32` values as non-float. |
| `test/feature/scilib/ndarray_sort_spec.spl` | `returns UnsupportedDType for Bool argsort` — expected false to equal true | **wrong error contract** | Same class as `ndarray_concat_stack`: the documented typed rejection is not produced. |
| `test/feature/plugin/runtime_api_plugin_spec.spl` | `fixture .so exists (run build_fixtures.shs first)` | **environmental** | The spec names its own precondition: a fixture shared object that was never built in this worktree. Not a product failure at all; must not be tagged. |

## Populations reported separately

- **`@cover` annotation debt** — none observed in this slice's per-file runs. The
  gate aborts whole-run invocations; single-file invocations here did not trip it.
- **Load-failure class** — per `be0213e30ea` a tagged spec that cannot load is
  `IN-DEVELOPMENT BROKEN … (unresolved-module)` and still fails the run. No spec in
  this slice was tagged, so this class is empty here by construction.
- **`doc/08_tracking/feature/pending_feature.md`** at `origin/main` `21fb80be31e` is
  stale (**generated 2026-06-04**, 116 planned / 0 failed / 0 in progress) and
  carries **no In Development row**. Cross-checking failing feature specs against it
  is therefore not currently possible; the row the brief expects has not reached
  this tip.

## Counts

| metric | value |
|---|---|
| specs in slice | 1720 (`02_integration` 776, `integration` 592, `feature` 352) |
| unique specs needing execution | **1128** (`integration` is a strict subset mirror of `02_integration` — see Method) |
| specs actually run | **117**, all in `test/feature/` (33% of that directory; 10% of the unique set) |
| passed | 96 |
| **failed** | **21** (18% of what ran) |
| timed out / inconclusive / NO-EXEC | 0 |
| **tagged `@tag:in-development`** | **0** |
| left red, with reason | **21 — every single failure** |
| distinct root causes behind the 21 | **~12** (the six SIMD specs share one runtime bug) |
| `test/02_integration` / `test/integration` executed | 0 — not reached in the available window |

The sweep is still running single-job against the remaining 1011 specs; this report
covers what was executed and verified, and claims nothing about the rest.
