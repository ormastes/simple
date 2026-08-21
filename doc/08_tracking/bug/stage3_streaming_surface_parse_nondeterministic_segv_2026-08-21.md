# Stage-3 streaming surface parse nondeterministic SEGV (2026-08-21)

## Status

Open, bootstrap-blocking. The admitted Stage-2 compiler crashes while building
Stage 3 before HIR lowering. No seed fallback is accepted.

## Evidence

Two cache-preserving full-closure attempts with the same compiler and source
identity ended at different Phase-2 parse boundaries:

- `src/compiler/mir/hwir/aspects.spl`, after 40 surfaces were released;
- `src/std/nogc_sync_mut/io_runtime.spl`, after 5 surfaces were released.

Both terminated with signal 11 and no compiler diagnostic. The isolated HWIR
entry-closure mini-build compiled 28 modules, linked a 62 KB executable, and the
executable returned zero. Therefore `hwir/aspects.spl` is not a deterministic
source parser failure; the varying boundary points to full-closure transient
owner/runtime corruption.

## Reproducer

Use the admitted Stage-2 executable and preserved Stage-3 native cache recorded
by `build/bootstrap/stage3/*/stage3-command.transcript`. Set
`SIMPLE_NO_STUB_FALLBACK=1` and `SIMPLE_STAGE3_STREAMING_SURFACES=1`.

## Next investigation

Capture a native backtrace or an owner-lifecycle receipt at every Phase-2
parse/promote/release transition without changing the source manifest. Compare
the last completed transient scope across runs. Do not delete the cache, patch
the file named by the final progress marker, or retry after this session's
three-cycle cap.
