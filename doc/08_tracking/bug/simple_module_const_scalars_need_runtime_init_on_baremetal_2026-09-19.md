# Module-level `const` scalars are emitted as `.bss` globals that need a runtime initializer

- **Filed:** 2026-09-19
- **Status:** OPEN (worked around at the C boundary, not fixed in codegen)
- **Area:** `70.backend` LLVM AOT codegen / module globals
- **Found while:** making SimpleOS Lite runnable on the Arduino UNO Q MCU (STM32U585, Cortex-M33)

## Symptom

`src/os/kernel/arch/cortex_m33/scalar_parser_fs_policy.spl` declares plain
scalar constants:

```simple
const CM33_FS_INIT_DONE: u32 = 0xffffffffu32
const CM33_FS_INIT_FILE_COUNT: u32 = 6
```

The emitted relocatable object does **not** fold them. They are merged into a
`.L_MergedGlobals` object placed in **`.bss`**, reached through a PC-relative
`R_ARM_REL32` load, and written only by a generated
`__module_init_<path>_dynamic` function:

```
00000000 <cm33_policy_fs_init>:
   ldr r1, [pc, #0xc]     @ -> .L_MergedGlobals (.bss)
   cmp r0, #5
   add r1, pc
   ldr r1, [r1]           @ reads 0 unless the module initializer ran
   it  hi
   movhi r0, r1
   bx  lr
```

On a baremetal target nothing calls that initializer, so every constant reads
as zero. `cm33_policy_fs_init(index)` then returns `0` instead of
`CM33_FS_INIT_DONE`, and the C bring-up shim's

```c
for (uint32_t index = 0;; index++) {
    uint32_t kind = cm33_policy_fs_init(index);
    if (kind == CM33_FS_INIT_DONE) break;
    ...
}
```

never terminates. Observed on QEMU MPS2-AN505 (Cortex-M33): boot stops silently
after `[TICK] SysTick enabled (~100 Hz)`, with no fault and no further output.

## Why it matters beyond this one file

A `const` scalar with a literal initializer is a compile-time value. Routing it
through mutable zero-initialised storage plus a runtime initializer:

- makes every such object depend on an initializer call that no freestanding
  consumer knows to make, and whose absence is silent (reads 0, not a fault);
- adds an extra exported symbol to an object whose admission gate
  (`scripts/check/check-cm33-scalar-parser-fs-object.shs`) deliberately pins the
  exact external symbol set — the generated initializer is why that gate had to
  be widened from 10 exports to 11;
- costs a PC-relative load plus a memory read per use where an immediate would do.

## Current workaround (landed)

`src/os/kernel/arch/cortex_m33/cm33_shim.c` now declares and calls
`__module_init_src_os_kernel_arch_cortex_m33_scalar_parser_fs_policy_spl_dynamic()`
before `faults_init()`, and the two object gates admit the initializer symbol.
That is correct for this consumer but does not remove the hazard for the next
freestanding consumer of a Simple object.

## Fix wanted

Fold module-level `const` scalars with literal initializers at compile time
(immediate operand, or `.rodata` when the address is taken), so an object that
declares only such constants exports no initializer and carries no `.bss`.

## Reproduce

```bash
sh scripts/os/build-cortex-m-policy-objects.shs thumbv8m.main-none-eabi build/os/cm33-policy
llvm-readobj --symbols build/os/cm33-policy/scalar_parser_fs_policy-thumbv8m.main-none-eabi.o \
  | grep -A6 MergedGlobals      # Section: .bss..L_MergedGlobals
```
