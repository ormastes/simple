# armv7 dynamic: Thumb B.W to imports and ARM TLS GD/LDM/LDO

- **status:** verification-pending (fail-closed only; feature not implemented)
- **found by:** Opus review of the armv7 dynamic linker commit (lane c)

## Defect
1. A `R_ARM_THM_JUMP24` (30) or `R_ARM_THM_JUMP19` (51) against an imported function was pointed at the ARM-state PLT entry and encoded as Thumb `B.W`. That branch enters ARM code in Thumb state and corrupts execution silently. ld.lld inserts a Thumb->ARM thunk here, for example for a tail call such as `b.w puts`.
2. `R_ARM_TLS_GD32` (104), `R_ARM_TLS_LDM32` (105) and `R_ARM_TLS_LDO32` (106) were classed as `RC_PCREL`. That computes S+A-P instead of building a GOT pair with `DTPMOD32`/`DTPOFF32`.

## Fix
`elf_reloc_scan` (`reloc_scan.spl`) now rejects both cases with `UnsupportedFeature`.

## Repro and prevention
`test/01_unit/compiler/backend/linker/elf_dynamic_tls_scan_spec.spl`, section "armv7 dynamic scan fail-closed".

## Open
- Implement the interworking thunk to the PLT.
- Implement the ARM TLS GD/LD GOT pairs.
