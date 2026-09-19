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

## Workaround in place

`examples/09_embedded/simple_os/arch/aarch64/limine_entry.spl` declares
`extern fn __simple_call_module_inits()` and calls it first in `_start`. The gate then passes
(`PASS — 4 boot-stage marker(s) checked ... 91 serial line(s)`).

This fixes one entry file. Every other freestanding entry in the tree has the same hole, and a new
one starts with it.

## Required fix

Emit the call from the freestanding boot path itself — either in the generated boot glue, or by
rooting `__simple_call_module_inits` as a `KEEP` target and calling it before the entry symbol — so
that no entry author has to know about it. Until then, a freestanding entry that relies on any
module-level initializer is silently broken.
