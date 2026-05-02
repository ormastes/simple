# x86 Bare-Metal Boot Specification

Tests for the x86 bare-metal boot infrastructure including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-BOOT-001 |
| Category | Bare-Metal / x86 |
| Status | In Progress |
| Source | `test/feature/usage/x86_boot_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests for the x86 bare-metal boot infrastructure including:
- Multiboot header generation
- GDT setup and loading
- Serial port initialization
- Test harness output

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/x86_boot/result.json` |

## Scenarios

- has correct magic number
- has correct flags
- checksum validates
- null descriptor is all zeros
- kernel code segment has correct access
- kernel data segment has correct access
- kernel code selector is 0x08
- kernel data selector is 0x10
- user code selector has RPL 3
- user data selector has RPL 3
- COM1 base address is 0x3F8
- COM2 base address is 0x2F8
- data register offset is 0
- line status register offset is 5
- 115200 baud divisor is 1
- 9600 baud divisor is 12
- formats hex addresses correctly
- multiboot section comes first
- success exit code (0) becomes (1)
- failure exit code (1) becomes (3)
- can decode QEMU exit code
