# Freestanding links never call `__simple_call_module_inits`, so module globals stay NULL

Status: OPEN for the general case (worked around per-entry; aarch64 Limine entry fixed)
Found: 2026-09-19, lane C3, booting the full SimpleOS aarch64 Limine kernel.

## Symptom

The full aarch64 Limine kernel linked and booted through EDK2/AAVMF -> Limine, printed its whole
boot transcript, and then stopped dead right after

```
[BOOT] PMM probe: allocated pfn=262156 free_pages_after=120346
```

with no trap message. Re-running the same ESP under `qemu-system-aarch64 ... -d int,guest_errors`
showed the reason:

```
Taking exception 4 [Data Abort] on CPU 0
...with ESR 0x25/0x96000007
...with FAR 0x8
...with ELR 0xffffffff80105d8c
...to EL1 PC 0x0
```

`llvm-nm`/`llvm-addr2line` put the ELR in `os__kernel__memory__pmm___pmm_remove_containing_page`.
`FAR 0x8` is a read through a NULL array handle: `pmm.spl`'s
`var g_pmm_contiguous_bases: [u64; 256] = [0; 256]` was never initialized.

## Cause

`_init_all.o` defines `__simple_call_module_inits`, which calls every `__module_init_<module>`. On
a hosted target the generated `main()` stub calls it
(`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs`). A freestanding link has no
`main()` stub, so nothing references it, `--gc-sections` drops it, and every module global that
needs a heap-boxed initializer keeps its `.bss` zero. `llvm-nm` on the kernel showed
`__simple_call_module_inits` absent and every `__module_init_*` as an undefined weak.

The writes in `_pmm_reset_contiguous_registry` hid the problem: `rt_array_set` on a non-array
returns 0, so resetting the registry is a silent no-op, and only the first READ faults.

## Fix

`examples/09_embedded/simple_os/arch/aarch64/limine_entry.spl` declares
`extern fn __simple_call_module_inits()` and calls it first in `_start`. The gate then passes
(`PASS — 4 boot-stage marker(s) checked ... 91 serial line(s)`).

**Correction (Fable review, 2026-09-19).** An earlier version of this record claimed every other
freestanding entry has the same hole. That is false, and the opposite is the point: calling it
explicitly is the tree convention, and the aarch64 Limine entry was the one that had not adopted
it. 19 files reference the symbol, including `arch/riscv64/boot/boot_entry.c:82,98` (weak
declaration plus a null-checked call), `arch/riscv64/gui_entry_desktop.spl:38,48` and the
`starfive`/x86_64 `crt0` paths. So this is a missing call in one entry, not a missing mechanism.

## Still open

The convention is unwritten and unenforced: nothing fails when a new freestanding entry omits the
call, and the failure mode is a NULL global that faults much later, far from the cause. Either emit
the call from the generated freestanding boot glue, or add a check that a freestanding entry
references the symbol.

See also `freestanding_entry_module_val_initializers_never_run_2026-07-06.md`, the same class one
level down: there `__module_init_*` was never EMITTED for entry-module `val`s, whereas here the
functions exist and are simply never called.
