# Stage-2 candidate regressions at b5d93e48cd8 (test-runner trait dispatch; CLI MIR SIGSEGV)

Date: 2026-11-14
Lane: work/release-1.0.0-mcp-local (MSVC), receipt-authorized full run (cycle 24d)
Baseline comparison: 189dabae8e3 (cycle 24b) — HIR fully green, MIR reached 79%
(1832/3148) before the 48 GiB ceiling; see
bootstrap_stage2_seed_parent_retention_oom_2026-10-22.md addendum.

Two NEW stage2-candidate regressions appeared between 189dabae8e3 and
b5d93e48cd8 (~250 commits of lane churn in between). Both block the slim
matrix harder than the known memory ceiling does.

## Regression 1: test_runner_build — native trait dispatch not object-safe

`test_runner_build` FAILs in ~403 s with MIR lowering errors:

```
[MIR error] native trait dispatch lacks object-safe method:
  compiler.common.data.attribute_schema_v1::AttrOwnerV1::owner_read
  at src/compiler/00.common/data/attribute_schema_v1.spl:70:31
[MIR error] native trait dispatch lacks object-safe method:
  ...AttrOwnerV1::owner_write at .../attribute_schema_v1.spl:92:25
[MIR error] native trait dispatch lacks object-safe method:
  ...AttrOwnerV1::owner_write at .../attribute_schema_v1.spl:113:35
error: in-process native-build: MIR lowering error: missing native trait
  implementation: ...AttrOwnerV1 for at .../attribute_schema_v1.spl:150:66
```

The test-runner closure pulls in compiler.common.data.attribute_schema_v1,
whose AttrOwnerV1 trait methods are rejected by the candidate's native
trait-dispatch object-safety check. This source file is recent lane work.

## Regression 2: compiler_cli_build — SIGSEGV (status 139) early in MIR

`compiler_cli_build` CRASHes with status 139 (SIGSEGV) at ~5,458 s, very
early in the MIR phase (128/3157 modules, right after aop_weave completed and
backend AOT evidence was retained):

```
[build] phase=aop_weave ... complete
[build] phase=native_cache ... complete
[NATIVE] codegen: 8 uncached module(s), concurrency=1
[build] phase=native_staged ... done=672 total=3157 ... current=batch-85
-> process exits 139 (no further output; no LLVM/HIR diagnostic)
```

At 189dabae8e3 the SAME row reached MIR 1832/3148 (crash-free). The segv is
new in the b5d93e48cd8 range and is not the known HirTypeKind defect (#9071,
fixed by the gen7 sweep and confirmed green at both tips' HIR phases) nor the
RSS ceiling (the watchdog summary shows the crash, not rss-cap-exceeded).

## Why filed together

Both are stage2-CANDIDATE (pure Simple) regressions introduced by the
fast-moving compiler lanes between the two tips; both are deterministic
within the receipt-authorized full-run lane (cycle 24d, mcp-local5). The
baseline corridor for the slim matrix remains 189dabae8e3 + the 48 GiB
ceiling question — these two defects make every tip AT or AFTER
b5d93e48cd8 strictly worse for the Windows stage2 lane until they are
fixed.

## Repro

Receipt-authorized full run per the 24a-24d recipe (fresh admission ->
stage4 receipt -> full run), or any stage2 slim-matrix campaign at
b5d93e48cd8 on the MSVC lane. Row logs:
build/bootstrap/mcp-local5/stage2-compiler-tests/x86_64-pc-windows-msvc/
verification/logs/{compiler_cli_build.log,test_runner_build.log}.

## Owner asks

1. AttrOwnerV1 (attribute_schema_v1.spl): make the trait methods
   object-safe for native dispatch, or provide the native trait
   implementation the lowering expects.
2. CLI-row MIR segv: the crash follows retained backend AOT evidence at
   .../cache/compiler-tools/stage2/d145d236.../899d555e.../simple-aot-diagnostic-*;
   that evidence bundle should localize the faulting module.

## 2026-11-15 addendum: Regression 2 ALSO reproduces at 189dabae8e3 — the "crash-free baseline" claim above is retracted

Cycle 25b (receipt-authorized full run, mcp-local lane, output c25full2):
tip 189dabae8e3 + ONLY the RSS-policy ceiling cherry-pick (9d94016901c,
scripts-only — cannot affect compiler codegen), MSVC, cap 54525952 KiB,
cold native cache (cached=0).

`compiler_cli_build` again exited 139 (SIGSEGV), at 6,562 s into the row,
MIR 650/3148 (20.6%), immediately after `aop_weave` completed (batch-81) at
the transition into `native_cache`:

```
[build] phase=aop_weave state=complete done=8/8 elapsed_ms=6556184
[build] phase=native_cache state=running done=0 total=8 ...
-> process exits 139 (no LLVM/HIR diagnostic)
```

Row self-report at the last MIR line: rss_mib=32876 (32.8 GiB) at MIR 650.
The watchdog did NOT report rss-cap-exceeded (exit 139, not 88), but the
row's RSS trajectory leaves a memory-pressure-corruption hypothesis open —
pre-ceiling cycles were killed by the watchdog at 48 GiB before any batch at
this depth ran far enough to expose it. Cycle 24b "reached MIR 1832
crash-free" is therefore NOT evidence that 189dabae8e3 is free of
Regression 2: outcomes at the same tip differ (1832 vs 650), so the segv is
either non-deterministic or cache/state-dependent (cycle 25b ran with a cold
native cache; cycle 24b's cache state was not recorded).

Consequence: every tip AT or AFTER 189dabae8e3 is blocked for the Windows
stage2 lane by Regression 2 (tips >= b5d93e48cd8 additionally by Regression
1). The lane's next corridor is the current release/1.0.0 tip, which carries
candidate fixes e250454f1aa (MIR erased-generic payload decoded exactly once
per consumer) and 10502b44377/92237f6276d (per-module AOT codegen errors
fail their module, not the worker), plus the memory reductions
(5f80235594b interface-only HIR + serial MIR sharding; 7074bd686e7
essential-backend closure shrink).

## 2026-11-15 addendum 2: cycle 26 at 43d32352d40 — same deterministic crash; the non-determinism hypothesis is retracted

Cycle 26 (receipt-authorized full run, clean tip 43d32352d40, no local
patches; 56 GiB cap per #9452; campaign 28800 s): `compiler_cli_build` again
CRASHed, status 139 at 5,802 s — `done=672 total=3186 current=batch-85`,
immediately after the serial in-process `[NATIVE] codegen: 8 uncached
module(s)` step of the native_compile batch whose first module is
`lib.common.ui.ios.builder`:

```
[build] phase=native_compile ... done=0 total=8 ... current=lib.common.ui.ios.builder
[NATIVE] codegen: 8 uncached module(s), concurrency=1 (serial lane in this process: backend session owns codegen)
[build] phase=native_staged ... done=672 total=3186 ... current=batch-85  -> exit 139
```

Cross-tip comparison (all receipt-authorized, MSVC, stage2-candidate):

- 189dabae8e3 (cycle 25b): crash at 6,562 s, MIR 650/3148, batch-81, after
  the same [NATIVE] codegen step; row self-report 32.8 GiB.
- b5d93e48cd8 (cycle 24d, this doc's original filing): crash at 5,458 s,
  128/3157 recorded, `native_staged ... done=672 total=3157 ... batch-85`.
- 43d32352d40 (cycle 26): crash at 5,802 s, done=672/3186, batch-85.

The `done=672` closure offset is CONSTANT across all three tips (batch
number varies with closure size). The crash is therefore DETERMINISTIC at a
fixed closure offset — addendum 1's "non-deterministic or
cache/state-dependent" hypothesis is retracted; prior cycles that "reached
MIR 1832" simply never completed the crashing batch's codegen step.

Candidate fixes CARRIED by 43d32352d40 did NOT fix it: e250454f1aa (MIR
erased-generic payload decoded exactly once per consumer) and
10502b44377/92237f6276d (per-module AOT codegen errors fail their module,
not the worker). The crash follows the serial native codegen of one specific
8-module batch (first module `lib.common.ui.ios.builder`) — the defect is in
the stage2 candidate's native codegen for that module/batch, not in MIR
decode or in error isolation.

Minimal-repro path (next debugger): extract the exact native-build argv the
`compiler_cli_build` row uses from scripts/bootstrap/bootstrap-phase-verification.shs,
then narrow the closure to the crashing batch's 8 modules (batch membership
is visible in the row log around the last `[NATIVE] codegen: 8 uncached
module(s)` line; the batch's earlier members include
lib.nogc_async_mut.database.feature_utils, lib.common.text_whitespace,
lib.nogc_sync_mut.ui.gui_renderer, lib.common.ui.wm_chrome_theme). The
admitted stage2 compiler and runtime snapshot are preserved under
build/bootstrap/pinned-src/pinned-43d32352d40d/build/bootstrap/c26s2/.
No WER application crash dump exists (ReportArchive/ReportQueue and the
output tree checked), so the stack must come from a debugger attached to the
standalone repro.

Memory wall status: definitively closed. With the 52/56 GiB ceilings
(#9396/#9452) the watchdog never fired in cycles 25b/26 (tree peaked ~32
GiB, well under cap); no RSS kill at any point. The ONLY blocker for the
Windows stage2 lane is this codegen SIGSEGV (plus Regression 1's AttrOwnerV1
object-safety at >= b5d93e48cd8, absent at 189dabae8e3, untested at
43d32352d40's test_runner row — which PASSED in cycle 26, so Regression 1
appears fixed by the native-trait lanes landing near #9563).
