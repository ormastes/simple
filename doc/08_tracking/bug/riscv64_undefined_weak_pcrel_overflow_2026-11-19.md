# riscv64: PC-relative relocation to an undefined weak symbol overflows above 4 GiB

- status: verification-pending
- found: 2026-11-19 (lane ssos), internal SimpleOS riscv64 user link of a C hello
  against `build/os/sysroot-riscv64/lib/libsimpleos_all.a`

## Symptom
`internal engine: object archive0(simpleos_cxxabi.o): relocation type 19 against
'simpleos_entropy_seed_u64' at 4294968110: RISC-V relocation rounded high part exceeds
signed 20-bit range`. ld.lld links the same inputs.

## Root cause
`elf_boot_link` resolved every undefined weak symbol to S = 0. The SimpleOS riscv64
user base is 0x100000000, so `S - P` for CALL_PLT needs a -4 GiB displacement.
ld.lld (`getRISCVUndefinedRelativeWeakVA`) resolves BRANCH, JAL, CALL, CALL_PLT,
RVC_BRANCH, RVC_JUMP and PLT32 against an undefined weak to the place itself
(`auipc ra,0; jalr ra`), which the guarded call never executes. aarch64 already had
the equivalent rule for branches.

## Fix
`src/compiler/70.backend/linker/elf/elf_boot_link.spl`: for those seven riscv types,
S = P - A for an undefined weak.

## Tests
- Repro: `elf_boot_link_riscv64_spec` "resolves CALL_PLT and JAL to an undefined weak
  symbol to the place, matching ld.lld" — fixture `riscv_boot/weak_undef_rv64.{S,o}`
  at 0x100000000, bytes = ld.lld 18 `--no-relax` output (RED before the fix).
- Similar pattern: the fixture also covers JAL and the beq/c.beqz/c.j forms (the
  assembler emits them as JAL to an unknown target).
- End to end: hello linked internally for riscv64 links; readelf vs lld below.

## Verification still needed
A U-mode boot of the internally linked user ELF (blocked: see
simpleos_user_elf_boot_blocked_aarch64_riscv64_2026-11-19.md).
