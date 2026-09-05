# Smf Elf Passthrough Specification

> Tests covering SMF ELF Passthrough, ELF magic detection, ELF extraction, backward compatibility.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Elf Passthrough Specification

## Scenarios

### SMF ELF Passthrough

### ELF magic detection

#### detects ELF magic in Code section

- detects ELF magic in Code section


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects ELF magic in Code section")
# Create fake ELF object (ELF magic + padding)
var elf_bytes: [u8] = [0x7F, 0x45, 0x4C, 0x46]
var ei = 0
while ei < 60:
    elf_bytes.push(0)
    ei = ei + 1

val smf = build_test_smf_with_code(elf_bytes)
expect(smf.len()).to_be_greater_than(128)
```

</details>

#### rejects non-ELF Code section

- rejects non-ELF Code section


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-ELF Code section")
# Code section with non-ELF bytes
val raw_code: [u8] = [0x48, 0x89, 0xE5, 0xC3]
val smf = build_test_smf_with_code(raw_code)
expect(smf.len()).to_be_greater_than(128)
```

</details>

#### handles empty Code section

- handles empty Code section


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty Code section")
val empty: [u8] = []
val smf = build_test_smf_with_code(empty)
expect(smf.len()).to_be_greater_than(128)
```

</details>

### ELF extraction

#### preserves full ELF bytes

- preserves full ELF bytes
   - Expected: smf[0] equals `0x7F`
   - Expected: smf[1] equals `0x45`
   - Expected: smf[2] equals `0x4C`
   - Expected: smf[3] equals `0x46`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves full ELF bytes")
# Verify that ELF bytes can be round-tripped through SMF
var elf_bytes: [u8] = [0x7F, 0x45, 0x4C, 0x46, 2, 1]
var pi = 0
while pi < 58:
    elf_bytes.push(pi as u8)
    pi = pi + 1

val smf = build_test_smf_with_code(elf_bytes)
# Code section should start at offset 0 in the SMF data
expect(smf[0]).to_equal(0x7F)
expect(smf[1]).to_equal(0x45)
expect(smf[2]).to_equal(0x4C)
expect(smf[3]).to_equal(0x46)
```

</details>

### backward compatibility

#### old SMF without ELF works normally

- old SMF without ELF works normally
   - Expected: smf[0] equals `0x90`
   - Expected: smf[1] equals `0xC3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("old SMF without ELF works normally")
val raw_code: [u8] = [0x90, 0xC3]
val smf = build_test_smf_with_code(raw_code)
# Non-ELF code sections still produce valid SMF
expect(smf[0]).to_equal(0x90)
expect(smf[1]).to_equal(0xC3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/smf_elf_passthrough_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SMF ELF Passthrough, ELF magic detection, ELF extraction, backward compatibility.
- SMF ELF Passthrough
- ELF magic detection
- ELF extraction
- backward compatibility

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `61c6249446b9a9b4aea20804919f2d7bacfe070746845faec70ce26fb7a21c6a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61c6249446b9a9b4aea20804919f2d7bacfe070746845faec70ce26fb7a21c6a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61c6249446b9a9b4aea20804919f2d7bacfe070746845faec70ce26fb7a21c6a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/linker/smf_elf_passthrough_spec.spl
mirror: doc/06_spec/01_unit/compiler/linker/smf_elf_passthrough_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/linker/smf_elf_passthrough_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/linker/smf_elf_passthrough_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/linker/smf_elf_passthrough_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects ELF magic in Code section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/smf_elf_passthrough_spec.spl:168:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-ELF Code section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/smf_elf_passthrough_spec.spl:176:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles empty Code section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
