# 32-bit native backend: pointer/handle width disagrees with the runtime extern table (arm32, riscv32) (2026-11-18)

- id: `baremetal_32bit_pointer_abi_backend_2026_11_18`
- severity: P2 (every 32-bit freestanding lane needs a per-arch workaround)
- status: open (workarounds landed; backend/extern-table fix not started)
- related: `baremetal_32bit_i64_pair_abi_mismatch_2026-11-17.md` (riscv32/i686 alignment side),
  `baremetal_arm32_aavmf32_no_esp_boot_2026-11-17.md`
- repro spec: `test/01_unit/compiler/70.backend/baremetal_32bit_pointer_abi_spec.spl`
  (`@tag:in-development`, expected RED)

## Defect

The runtime extern table (`bm_rt.spl`) declares pointers and text handles as `i64`
(`rt_println_str(ptr: i64, len: i64)`, `rt_strcat_tagged(a: i64, b: i64)`). On 32-bit targets
the native backend emits the pointer/handle as ONE 32-bit register and never sets the second
register of the pair, so a callee that follows the declared signature reads garbage.

Measured with `llvm-objdump -dr main.o` of `examples/09_embedded/freestanding_hello`:

- arm32 (`armv7-unknown-none`): `ldr r0,..; mov r2,#28; mov r3,#0; bl rt_println_str`.
  ptr = r0 only, len = r2:r3 (AAPCS even-pair alignment is correct). A callee built from
  `bm_rt.spl` reads ptr as r0:r1 with r1 = stale -> data abort at a bogus address
  (observed: AAVMF32 abort at PC 0x5CB1C034 right after the first print).
- riscv32 (`riscv32-unknown-none`): ptr = a0, len = a1:a2 (no even-pair alignment).

## Current workarounds (to delete when fixed)

- arm32: `crt0_arm32.S` shims (`mov r1,#0; b bm32_<name>`; `rt_strcat_tagged` moves r1 to r2:r3)
  and the `bm32_` rename in `check-baremetal-efi-boot.shs`.
- riscv32/i686: `bm_rt32.spl` declares the real widths (i32 handles, `len` + `len_hi`); it
  encodes the backend's CURRENT packing, so it breaks the day the backend aligns pairs. It does
  not fit arm32 (even-pair alignment), which is why arm32 needed the shims instead.

## Fix plan

1. Pick one rule: either the extern table declares real pointer width per target
   (`usize`-like `ptr` type), or the backend zero-extends handles to the declared i64 pair.
   Prefer the first: a pointer type in the extern table makes one `bm_rt.spl` serve all arches.
2. Align i64 args to even register pairs on ilp32/AAPCS in the backend (riscv32 side).
3. Delete the arm32 shims, `bm32_` rename and `bm_rt32.spl`; the repro spec must go green and
   its `@tag:in-development` header be removed.
4. Pin with the boot check on riscv32, i686 and arm32 (exact transcript).

Similar-pattern tests: `rt_strcat_tagged`, `rt_string_new*`, `rt_string_data/len`, `rt_panic`
(all pointer/handle params), and `rt_raw_i64_to_string` (genuine i64).
