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
