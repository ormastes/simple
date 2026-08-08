# rv32 OS boot hang: rt_as_heap low-pointer load fault in early boot (FIXED)

**Date:** 2026-06-30
**Area:** freestanding RISC-V runtime (`src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`, shared by rv32 via `baremetal_stubs.c`)
**Severity:** high — silently hung the **entire** rv32 OS boot before heap/services init.
**Status:** FIXED (the crash class). One upstream value-representation question remains (below).

## Symptom

The rv32 kernel (`build/os/simpleos_riscv32.elf`, entry `src/os/kernel/arch/riscv32/boot.spl`)
booted through the banner + `LOG OK`/`MEM OK`/`PMM OK` and then **silently hung** — never reaching
`HEAP OK`, `SVC OK`, `BOOT OK`, or `os_main`. The existing `nvme_rv32_baremetal_boot_spec`
(asserts `HEAP OK`/`SVC OK`) would fail against a freshly built ELF.

## Diagnosis (measured, not inferred)

UART markers placed around each `boot_main` step localized the stop to **inside**
`riscv_noalloc_heap_init` (both `rt_riscv_qemu_heap_start/size` args evaluated fine; the call
entered but never printed `HEAP OK`/`HEAP FAIL`). Since `heap_init` is straight-line arithmetic
(cannot loop), this had to be a trap. `qemu-system-riscv32 -d int` confirmed:

```
riscv_cpu_do_interrupt: cause:5 (load access fault), epc:0x8000a940, tval:0x8
... then cause:1 (fault_fetch) at epc:0 forever  (no trap vector installed this early)
```

`epc 0x8000a940` maps to **`rt_as_heap`**, instruction `lbu a0, 0(a0)` reading
`header->object_type` with `header == 0x8`. A heap-**tagged** value (`raw & 7 == TAG_HEAP`) whose
masked pointer is tiny (here `~0x9` → header `0x8`) passed the guard, which only rejected
`header == 0`. The load from `0x8` (unmapped) faulted; with no trap vector yet, the CPU jumped to
`0x0` and looped on fetch faults → silent hang.

## Fix

`rt_as_heap` now rejects null **and** sub-`0x10000` headers — the same threshold the function's
untagged branch already enforces (a real heap object lives at `0x80000000+`, never below
`0x10000`):

```c
if (!header || (spl_u64)header < 0x10000ULL || header->object_type != kind) {
    return (RtHeapHeader *)0;
}
```

This is a legitimate invariant, not a workaround: an invalid low pointer must never be dereferenced
as a heap header. It is in the shared runtime, so it hardens rv64 too (the rv64 lane overrides the
weak siblings but uses this `rt_as_heap`).

## Verified

With the guard, the rv32 kernel boots to completion under `qemu-system-riscv32 -bios none -smp 3`:
`SimpleOS RV32` → `SMP harts: 3` → `LOG OK` → `MEM OK` → `PMM OK` → `HEAP OK` → `SVC OK` →
`BOOT OK` → reaches `os_main`. No regression on the rv64 build.

## Remaining upstream question (separate, lower priority)

*Why* a malformed heap-tagged value (`~0x9`) reaches `rt_as_heap` during `heap_init` is not yet
root-caused. The likely trigger is the module-level `val NOALLOC_HEAP_ALIGN: u64 = 8` reading as a
garbage tagged value in baremetal (cf. the known "module-level val zero in baremetal" class) and a
u64 comparison routing through a generic value path that probes operands with `rt_as_heap`. The
guard makes this safe (the bad value is rejected as "not a heap object", which boot handles
gracefully), but the value-representation path is worth a dedicated look. Tracked as follow-up.

## Note: missing canonical rv32-kernel build path

While diagnosing, confirmed there is **no CLI path that builds the rv32 kernel smoke target**
(`get_target` / `boot.spl` → `simpleos_riscv32.elf`): `simple os build/run/test --arch=riscv32`
all use `get_qemu_target` (the fs-exec `smoke_entry.spl` lane), and the qemu boot specs only
`SKIP` when the ELF is absent. That missing path is why the prebuilt ELF kept going stale. The
working recipe is the full-source kernel build documented in
`doc/08_tracking/bug/native_build_rv32_baremetal_silent_255_2026-06-30.md`.
