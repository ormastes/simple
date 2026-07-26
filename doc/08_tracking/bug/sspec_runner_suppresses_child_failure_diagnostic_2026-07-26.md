# SSpec runner suppresses the failing child diagnostic

**Status:** open
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
