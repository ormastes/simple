# Fat32 Lfn Parse Specification

> Tests covering fat32 LFN parser — single-slot ASCII name.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fat32 Lfn Parse Specification

## Scenarios

### fat32 LFN parser — single-slot ASCII name

#### decodes one ASCII code unit

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- decodes one ASCII code unit
   - Expected: ch equals `l`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("decodes one ASCII code unit")
val slot = _make_libllvm_so_slot()
val ch = fat32_decode_lfn_code_unit(slot, 1)
expect(ch).to_equal("l")
```

</details>

#### returns empty string for 0x0000 padding

- returns empty string for 0x0000 padding
   - Expected: ch equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty string for 0x0000 padding")
val slot = _make_libllvm_so_slot()
# Byte offset 24 is char 11 (0x0000 NUL terminator after 'o')
val ch = fat32_decode_lfn_code_unit(slot, 24)
expect(ch).to_equal("")
```

</details>

#### returns empty string for 0xFFFF padding

- returns empty string for 0xFFFF padding
   - Expected: ch equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty string for 0xFFFF padding")
val slot = _make_libllvm_so_slot()
# Byte offset 28 is char 12 (0xFFFF padding)
val ch = fat32_decode_lfn_code_unit(slot, 28)
expect(ch).to_equal("")
```

</details>

#### assembles libLLVM.so from a single slot

- assembles libLLVM.so from a single slot
   - Expected: name equals `libLLVM.so`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("assembles libLLVM.so from a single slot")
val slot = _make_libllvm_so_slot()
val name = fat32_parse_lfn_slot(slot, 0)
expect(name).to_equal("libLLVM.so")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/fat32_lfn_parse_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering fat32 LFN parser — single-slot ASCII name.
- fat32 LFN parser — single-slot ASCII name

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `e54457a834deed2f2c9633a30b33afeb378301e7735135db7120ca2ef74d5ee2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e54457a834deed2f2c9633a30b33afeb378301e7735135db7120ca2ef74d5ee2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e54457a834deed2f2c9633a30b33afeb378301e7735135db7120ca2ef74d5ee2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/fat32_lfn_parse_spec.spl
mirror: doc/06_spec/03_system/os/fat32_lfn_parse_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/fat32_lfn_parse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/fat32_lfn_parse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/fat32_lfn_parse_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes one ASCII code unit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/fat32_lfn_parse_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty string for 0x0000 padding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/fat32_lfn_parse_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty string for 0xFFFF padding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
