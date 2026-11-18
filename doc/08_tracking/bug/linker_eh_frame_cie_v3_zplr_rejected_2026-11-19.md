# Linker: .eh_frame CIE version 3 and zPLR augmentation rejected

- **status:** verification-pending (fixed in PR #10268)
- **found by:** rv64 glibc dynamic/PIE/static link of hello_libc (simplelink lane)

## Defect
`_eh_cie_encoding` (`src/compiler/70.backend/linker/elf/eh_frame_hdr.spl`) accepted only CIE version 1 with augmentation `zR`. glibc's riscv64 crt objects carry version-3 CIEs and `zPLR`, so the link failed with `UnsupportedFeature: .eh_frame CIE version 3` and then with `augmentation 'zPLR'`.

## Fix
- Version 3 is accepted. It differs from version 1 only in using a ULEB return register.
- The `z` augmentation data is now walked: `P` (an encoding byte plus a pointer of that encoding), `L` and `R`. Unknown letters still fail closed.
- Known limit: an `absptr` personality is assumed to be 8 bytes, which is wrong for ELF32. rv32 dynamic is not admitted yet.

## Repro and prevention
`test/01_unit/compiler/backend/linker/elf_riscv64_dynamic_spec.spl`: "indexes an FDE under a version-3 zPLR CIE".
