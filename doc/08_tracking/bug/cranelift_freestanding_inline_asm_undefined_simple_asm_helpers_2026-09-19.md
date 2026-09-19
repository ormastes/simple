# Cranelift lowers `asm volatile` to undefined `__simple_asm_H*` helpers, so no pure-Simple HAL links

Status: OPEN (recorded, not fixed)
Found: 2026-09-19, lane C3, trying to link the pure-Simple `arch/arm64/cpu.spl` twin.
Related: `inline_asm_colon_operands_not_parsed_2026-08-26.md` (parsing); this one is codegen.

## Symptom

`src/os/kernel/arch/arm64/cpu.spl` at `eb2781abc3b` ("fix(sffi): remove unbacked privileged cpu
bridges") implements the AArch64 system-register surface as pure Simple inline asm — the shape
`doc/07_guide/os/hal/pure_simple_hal.md` asks for. Merge `e274cd33719` clobbered it back to
`extern fn rt_arm64_*` declarations.

Restoring the inline-asm version and rebuilding the aarch64 Limine kernel:

```sh
SIMPLE_BOOTSTRAP=1 <seed> native-build --backend cranelift --entry-closure \
  --entry examples/09_embedded/simple_os/arch/aarch64/limine_entry.spl \
  --target aarch64-unknown-none-elf --linker-script .../linker_limine.ld -o kernel.elf
...
Build failed: link failed: ld.lld: error: undefined symbol: __simple_asm_H09bc53621729a65a
```

Every `asm volatile` block becomes a call to a per-block `__simple_asm_H<hash>` symbol that nothing
defines, so the pure-Simple HAL cannot be linked on the cranelift freestanding lane at all.

## Impact

The policy in `doc/07_guide/os/hal/pure_simple_hal.md` (pure Simple first; inline asm only for
architecturally irreplaceable ops, which MSR/MRS and barriers are) is unreachable on this lane. The
C boundary is the only option, which is why the 19 accessors now live in
`examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c` with the Simple twin
recorded as the source of their instruction text.

## Required fix

Lower an inline-asm block in the cranelift backend to the instructions themselves, or emit a
definition for the `__simple_asm_H*` helper it calls. Then move the 19 accessors back to
`cpu.spl` and delete the C copies.
