# FR-RISCV-TP-INIT-2026-05-02: Wire tp Register at Baremetal Boot for Per-CPU Base

## Why

AC-4 of `riscv_smp_cache_hal_phase1` requires that each hart writes its per-CPU
base address into the `tp` (thread pointer / x4) register before entering the
kernel entry point.  The production helpers (`simulate_tp_write_baremetal`,
`read_tp_test`, etc.) have landed in `src/os/kernel/arch/riscv64/per_cpu.spl`
and are verified by `test/unit/os/kernel/arch/riscv/per_cpu_tp_spec.spl`.

The actual boot-time write of `tp` must happen in `start.S` (or equivalent
baremetal stubs).  The relevant files are currently modified by an in-flight
track and cannot be edited:

- `examples/simple_os/arch/riscv64/boot/baremetal_stubs.c` — dirty in `jj st`
- `examples/simple_os/arch/riscv64/boot/ghdl_boot_info_runtime.c` — dirty in `jj st`

This FR records the exact change needed so it is not lost when those files
reach a clean state on main.

## What

### start.S / baremetal entry — sequence to add after sp setup

After the hart stack pointer (`sp`) is set up and before the call to
`__spl_start_bare`, add the following sequence for each hart:

```asm
# Set tp = &per_cpu_data[mhartid]
# Assumes per_cpu_base_array is a symbol pointing to the base-pointer array.
csrr  a0, mhartid              # a0 = hart ID
la    a1, per_cpu_base_array   # a1 = &per_cpu_base_array[0]
slli  a0, a0, 3                # a0 = hart_id * 8  (64-bit pointer stride)
add   a1, a1, a0               # a1 = &per_cpu_base_array[hart_id]
ld    a1, 0(a1)                # a1 = per_cpu_base_array[hart_id]
mv    tp, a1                   # tp = per-CPU base for this hart
```

For rv32 the stride is 4 bytes and `lw` replaces `ld`:

```asm
csrr  a0, mhartid
la    a1, per_cpu_base_array
slli  a0, a0, 2                # 32-bit pointer stride
add   a1, a1, a0
lw    a1, 0(a1)
mv    tp, a1
```

### Trap frame — x4 (tp) save slot

`x4` is `tp`.  In the trap entry save block (where `sd xN, 8*N(sp)` saves all
registers), tp must be explicitly saved:

```asm
sd    x4, 8*4(sp)    # save tp (x4) at slot 4 in the trap frame
```

And restored at trap exit:

```asm
ld    x4, 8*4(sp)    # restore tp (x4) from slot 4
```

This matches the `TrapFrameTest.regs[4]` index verified in `per_cpu_tp_spec.spl`.

## When

Apply this change after both of the following are true:

1. `examples/simple_os/arch/riscv64/boot/baremetal_stubs.c` and
   `examples/simple_os/arch/riscv64/boot/ghdl_boot_info_runtime.c` are clean
   (not modified by any in-flight track) on main.
2. A `per_cpu_base_array` symbol (or equivalent) is defined in the kernel BSS
   by the linker script.

## Acceptance

AC-4 in `.sstack/riscv_smp_cache_hal_phase1/state.md` flips from:

> PARTIAL — tp helpers landed; baremetal boot wiring deferred to FR-RISCV-TP-INIT-2026-05-02.

to:

> DONE — tp wired at baremetal boot; trap frame saves/restores x4.

Cross-link: `src/os/kernel/arch/riscv64/per_cpu.spl` (helpers), `test/unit/os/kernel/arch/riscv/per_cpu_tp_spec.spl` (specs).
