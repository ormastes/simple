# Linker: RISC-V static link rejects undefined weak TLS symbols

- **status:** verification-pending (fixed in PR #10268)
- **found by:** rv64 static glibc link (`_nl_current_LC_COLLATE`, simplelink lane)

## Defect
`elf_riscv_validate_tls_definition` required every RISC-V TLS relocation target to be defined. Static glibc has weak undefined TLS symbols, so the link failed with `RISC-V TLS relocation requires a defined TLS symbol: _nl_current_LC_COLLATE`.

## Fix
In a static link, an undefined weak TLS symbol (`SYMREF_WEAK_ZERO`) now resolves to tprel 0, as in ld.lld. This covers both local-exec and the initial-exec GOT slot. A strong undefined TLS symbol still errors.

## Repro and prevention
- The static glibc hello links and runs under qemu-riscv64, printing `hello libc 1 tls=8`.
- `elf_riscv64_dynamic_spec.spl` "riscv64 static" exercises the static path.
- No unit spec isolates the weak-TLS case yet. A follow-up is to add a fixture with a weak TLS reference.
