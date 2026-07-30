# Bug: Stage2 RV64 full-GUI closure requires hosted runtime APIs

**ID:** stage2-rv64-full-gui-runtime-closure-2026-07-30
**Severity:** blocker for `SIMPLEOS_STAGE2_FONT`
**Checkpoint:** `2a7e354c116ea1d9a948bf94d5a26c4d0238eed6`

## Result

Current-checkpoint Stage2 attempt 24 and scoped-tool attempt 12 are admitted.
RV64 attempt 25 compiles the canonical `_boot_full_gui_runtime.o`, but the
production `gui_entry_desktop.spl` object graph has a 618-symbol unresolved
pre-GC surface: 597 raw `rt_*` APIs, six qualified symbols, and fifteen other
symbols. lld proves at least twenty are live before its error limit. The raw
surface includes hosted or unrelated CUDA, Metal, OpenCL, SQLite, file/time,
and platform-backend APIs.

Attempt 25 exited 1 in `3:21.66` at `371,200 KiB` maximum RSS. The
freestanding precheck reported `622 unexpected / 615 deferred`; lld then
stopped after twenty live undefined symbols. Evidence is retained at
`/tmp/simple-font-rv64-attempt25-stage/evidence/`.

## Root cause and required fix

Native `--entry-closure` follows module imports, not function liveness. The
canonical desktop imports hosted and unrelated backend modules whose extern
runtime APIs are unavailable on RV64 freestanding. One coherent owner fix must
localize those imports behind hosted/backend adapters or provide real
current-ABI freestanding owners for APIs genuinely used by the RV64 product.

Do not enable freestanding stub fallback, restore the legacy mixed-ABI
`baremetal_stubs.c`, or add NIL/no-op shims. Those paths can create a
misleading ELF and violate the fail-closed contract. See
`simpleos_freestanding_weak_rt_stubs_fail_open_2026-07-27.md`.

## Resume

After a focused closure/provider gate proves the owner repair, run exactly one
fresh RV64 attempt 26 with `SIMPLE_NO_STUB_FALLBACK=1`. Only a validated ELF
unblocks QEMU crop calibration, exact-ten attempt 12, and manual attempt 2.

## Owner repair prepared

The current working change narrows the RV64 GUI entry closure to 45 modules.
Dedicated RV64 owners now cover the font FAT32 mount/read path, baremetal shell,
framebuffer Engine2D factory, and dependency-free input event types. Import
closure no longer reaches `vfs_init.spl`, `vfs_boot_init.spl`,
`os.kernel.boot.cpu`, or `nogc_sync_mut/diag.spl`. The focused Rust closure and
runtime-selector gate passes 2/2, both direct-runtime guards pass, and
`doc/06_spec` contains zero executable specs.

This is source/focused-gate evidence only. It does not close the bug until a
fresh clean-checkpoint Stage2/tool admission and the single reserved RV64
attempt 26 produce and validate the canonical ELF.
