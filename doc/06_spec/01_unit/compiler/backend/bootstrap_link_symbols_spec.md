# Bootstrap Link Symbols Specification

> Tests covering bootstrap link symbols.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Link Symbols Specification

## Scenarios

### bootstrap link symbols

#### emits bit-exact PTX float constants without primitive to_hex calls

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits bit-exact PTX float constants without primitive to_hex calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits bit-exact PTX float constants without primitive to_hex calls")
var builder = PtxBuilder__create((8, 6))
builder.emit_const_float("%f0", PrimitiveType.F32, 1.0)
builder.emit_const_float("%d0", PrimitiveType.F64, -2.5)
val ptx = builder.build()

expect(ptx).to_contain("mov.f32 %f0, 0F3F800000;")
expect(ptx).to_contain("mov.f64 %d0, 0DC004000000000000;")
```

</details>

#### maps relocation enums to architecture ABI values

- maps relocation enums to architecture ABI values
   - Expected: elf_reloc_type_to_elf_value(ElfRelocType.X86_64_PLT32) equals `4`
   - Expected: elf_reloc_type_to_elf_value(ElfRelocType.AArch64_Call26) equals `283`
   - Expected: elf_reloc_type_to_elf_value(ElfRelocType.Riscv_PcrelLo12I) equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps relocation enums to architecture ABI values")
expect(elf_reloc_type_to_elf_value(ElfRelocType.X86_64_PLT32)).to_equal(4)
expect(elf_reloc_type_to_elf_value(ElfRelocType.AArch64_Call26)).to_equal(283)
expect(elf_reloc_type_to_elf_value(ElfRelocType.Riscv_PcrelLo12I)).to_equal(24)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/bootstrap_link_symbols_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bootstrap link symbols.
- bootstrap link symbols

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b05ff0d8c928f0e7b103c04e663b800debb0be79205b309aba36cfda128c4acc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b05ff0d8c928f0e7b103c04e663b800debb0be79205b309aba36cfda128c4acc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b05ff0d8c928f0e7b103c04e663b800debb0be79205b309aba36cfda128c4acc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/backend/bootstrap_link_symbols_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/bootstrap_link_symbols_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/bootstrap_link_symbols_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/bootstrap_link_symbols_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/bootstrap_link_symbols_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/backend/bootstrap_link_symbols_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits bit-exact PTX float constants without primitive to_hex calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/bootstrap_link_symbols_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps relocation enums to architecture ABI values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
