# Cranelift emits garbage data pointer for [u8] array literals under freestanding native-build

## Status
Open.

## Severity
High — array payload unreachable; code injection into ring-3 completely blocked.

## Summary
`[u8]` array-literal data pointers are garbage under freestanding x86_64-unknown-none cranelift native-build. Array[0] read 0x30 instead of expected instruction 0x66. vmm_copy_bytes_to_phys copied nothing; target page remained zeroed; ring-3 executed 00 00 → #PF e=0005 CR2=0 (instruction fetch from NULL).

Discovered while injecting ring-3 entry code into guest memory in `ring3_smoke_entry.spl`.

## Evidence
- **Failure site**: `examples/09_embedded/simple_os/arch/x86_64/ring3_smoke_entry.spl _write_hello_code()` — array literal `[u8]{0x66, 0x48, ...}` (POP RAX XCHG RAX RBX...) had garbage pointer.
- **Discovery commits**: 12bddd3d29a1, 074fa56278f1 — ring-3 USEROK smoke injected test code via array literal.
- **Workaround in place**: wrote machine code as 5 LE u64 words via `mmio_write64` instead of array literal (commit 074fa56278f1).
- **Symptom**: array[0] read 0x30 (random), not 0x66; code copy never happened; CPU executed 00 00 at ring-3 entry point → #PF at CPL3.

## Failure Scenario
Ring-3 attempted to execute injected machine code but found NULL pointer → instruction fetch from NULL (CR2=0, e=0005 page protection). Kernel could not bootstrap user-mode execution.

## Impact
Any freestanding entry code using `[u8]` array literals for embedded machine code or data tables cannot access payload. Blocks ring-3 USEROK smoke.

## Next Step
Investigate cranelift lowering of array-literal data placement. Check `.rodata` section generation and relocation handling for freestanding targets. Data pointer may be misaligned or pointing to wrong section.
