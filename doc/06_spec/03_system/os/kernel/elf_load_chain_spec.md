# Elf Load Chain Specification

> Tests covering ELF Loader — magic validation, ELF Loader — valid ELF64 x86_64 header, ELF Loader — valid ELF64 RISC-V header, ElfImage — struct accessors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Elf Load Chain Specification

## Scenarios

### ELF Loader — magic validation

#### rejects empty bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects empty bytes
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects empty bytes")
val bytes: [u8] = []
val result = load_user_executable(bytes, Architecture.X86_64)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects too-short bytes

- rejects too-short bytes
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects too-short bytes")
val bytes: [u8] = [0x7F, 0x45, 0x4C]
val result = load_user_executable(bytes, Architecture.X86_64)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects invalid magic

- rejects invalid magic
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects invalid magic")
val bytes = _make_bytes(64, 0)
val result = load_user_executable(bytes, Architecture.X86_64)
expect(result.is_err()).to_equal(true)
```

</details>

### ELF Loader — valid ELF64 x86_64 header

#### parses minimal valid ELF64 x86_64 header

- parses minimal valid ELF64 x86_64 header
   - Expected: result.is_ok() is true
   - Expected: image.entry > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses minimal valid ELF64 x86_64 header")
val bytes = _make_minimal_elf64_x86()
val result = load_user_executable(bytes, Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val image = result.unwrap()
expect(image.entry > 0).to_equal(true)
```

</details>

### ELF Loader — valid ELF64 RISC-V header

#### parses minimal valid ELF64 RV64 header

- parses minimal valid ELF64 RV64 header
   - Expected: result.is_ok() is true
   - Expected: image.entry > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses minimal valid ELF64 RV64 header")
val bytes = _make_minimal_elf64_rv64()
val result = load_user_executable(bytes, Architecture.Riscv64)
expect(result.is_ok()).to_equal(true)
val image = result.unwrap()
expect(image.entry > 0).to_equal(true)
```

</details>

### ElfImage — struct accessors

#### ElfLoadSegment stores fields correctly

- ElfLoadSegment stores fields correctly
   - Expected: seg.file_offset as i64 equals `0x1000`
   - Expected: seg.virt_addr as i64 equals `0x400000`
   - Expected: seg.mem_size > seg.file_size is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ElfLoadSegment stores fields correctly")
val seg = ElfLoadSegment(
    file_offset: 0x1000,
    file_size:   0x200,
    virt_addr:   0x400000,
    mem_size:    0x300,
    flags:       5,
    align:       0x1000
)
expect(seg.file_offset as i64).to_equal(0x1000)
expect(seg.virt_addr as i64).to_equal(0x400000)
expect(seg.mem_size > seg.file_size).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/kernel/elf_load_chain_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ELF Loader — magic validation, ELF Loader — valid ELF64 x86_64 header, ELF Loader — valid ELF64 RISC-V header, ElfImage — struct accessors.
- ELF Loader — magic validation
- ELF Loader — valid ELF64 x86_64 header
- ELF Loader — valid ELF64 RISC-V header
- ElfImage — struct accessors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `31422052e3c7d50fd8888a7d1c54c89c346f004ed59d83262d498d02290858da`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `31422052e3c7d50fd8888a7d1c54c89c346f004ed59d83262d498d02290858da`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `31422052e3c7d50fd8888a7d1c54c89c346f004ed59d83262d498d02290858da`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/kernel/elf_load_chain_spec.spl
mirror: doc/06_spec/03_system/os/kernel/elf_load_chain_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/kernel/elf_load_chain_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/kernel/elf_load_chain_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/kernel/elf_load_chain_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects empty bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/kernel/elf_load_chain_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects too-short bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/kernel/elf_load_chain_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid magic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
