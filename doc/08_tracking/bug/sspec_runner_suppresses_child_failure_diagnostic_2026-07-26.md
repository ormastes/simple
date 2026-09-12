# SSpec runner suppresses the failing child diagnostic

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
**Found:** 2026-07-26
**Area:** app/test_runner / deployed CLI
**Blocks:** fresh verification of the WM/Web CPU glass material slice

## Symptom

Three bounded attempts to run
`test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_glass_material_spec.spl`
reported only `0 passed, 1 failed`. The child assertion, parse, import, or
runtime diagnostic was not forwarded, including with an absolute
`SIMPLE_LIB`. A direct `run` of the spec is not an equivalent diagnostic
route because it does not install the SSpec DSL.

The linked worktree also lacks its local `bin/simple` launcher. Running the
repository launcher from the primary checkout resolves to a binary that
identifies itself as the Rust bootstrap seed and then reports unrelated
compiler-tree diagnostics. Repository policy and the user instruction forbid
using that seed output as product verification or rebuilding/bootstraping just
to clear this feature checkpoint.

## Impact

The focused specs define real assertions, but this session cannot distinguish
a source failure from a harness/import failure. The source checkpoint must
remain **SOURCE PREPARED / UNVERIFIED**. No host, device, or QEMU admission may
be inferred from the opaque summary.

## Required fix and acceptance

The pure-Simple test runner must retain the child exit status and forward a
bounded diagnostic containing the failing file, scenario, and assertion or
compile error. Acceptance requires one intentionally passing and one
intentionally failing minimal SSpec, executed by the same deployed
pure-Simple binary, with the failing child message visible and no seed
delegation. This WM/Web lane will consume that repair but will not implement a
parallel runner or bootstrap the toolchain.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
