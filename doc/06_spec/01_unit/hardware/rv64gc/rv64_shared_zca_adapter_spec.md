# Rv64 Shared Zca Adapter Specification

> Tests covering RV64C shared Zca adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv64 Shared Zca Adapter Specification

## Scenarios

### RV64C shared Zca adapter

#### uses the common C.EBREAK, C.NOP, and C.ADDI rows

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the common C.EBREAK, C.NOP, and C.ADDI rows
   - Expected: ebreak.insn equals `0x00100073`
   - Expected: rvc_expand(0x0001).insn equals `0x00000013`
   - Expected: rvc_expand(0x0505).insn equals `0x00150513`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("uses the common C.EBREAK, C.NOP, and C.ADDI rows")
val ebreak = rvc_expand(0x9002)
expect(ebreak.compressed).to_be(true)
expect(ebreak.legal).to_be(true)
expect(ebreak.insn).to_equal(0x00100073)
expect(rvc_expand(0x0001).insn).to_equal(0x00000013)
expect(rvc_expand(0x0505).insn).to_equal(0x00150513)
```

</details>

#### continues to fail closed for the shared all-zero reservation

- continues to fail closed for the shared all-zero reservation
   - Expected: zero.insn equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("continues to fail closed for the shared all-zero reservation")
val zero = rvc_expand(0x0000)
expect(zero.compressed).to_be(true)
expect(zero.legal).to_be(false)
expect(zero.insn).to_equal(0)
```

</details>

#### keeps RV64-only integer forms in the shared RV64 specialization

- keeps RV64-only integer forms in the shared RV64 specialization
   - Expected: rvc_expand(0x6480).insn equals `0x0084B403) # C.LD`
   - Expected: rvc_expand(0xE880).insn equals `0x0084B823) # C.SD`
   - Expected: rvc_expand(0x35FD).insn equals `0xFFF5859B) # C.ADDIW`
   - Expected: rvc_expand(0x9C05).insn equals `0x4094043B) # C.SUBW`
   - Expected: rvc_expand(0x9C25).insn equals `0x0094043B) # C.ADDW`
   - Expected: rvc_expand(0x6522).insn equals `0x00813503) # C.LDSP`
   - Expected: rvc_expand(0xE42A).insn equals `0x00A13423) # C.SDSP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("keeps RV64-only integer forms in the shared RV64 specialization")
expect(rvc_expand(0x6480).insn).to_equal(0x0084B403) # C.LD
expect(rvc_expand(0xE880).insn).to_equal(0x0084B823) # C.SD
expect(rvc_expand(0x35FD).insn).to_equal(0xFFF5859B) # C.ADDIW
expect(rvc_expand(0x9C05).insn).to_equal(0x4094043B) # C.SUBW
expect(rvc_expand(0x9C25).insn).to_equal(0x0094043B) # C.ADDW
expect(rvc_expand(0x6522).insn).to_equal(0x00813503) # C.LDSP
expect(rvc_expand(0xE42A).insn).to_equal(0x00A13423) # C.SDSP
```

</details>

#### retains RV64 C legality distinctions without a runtime XLEN selector

- retains RV64 C legality distinctions without a runtime XLEN selector


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-HARDWARE
step("retains RV64 C legality distinctions without a runtime XLEN selector")
expect(rvc_expand(0x2085).legal).to_be(true) # C.ADDIW, RV64 only
expect(rvc_expand(0x6001).legal).to_be(false) # C.LUI x0 reserved
expect(rvc_expand(0x1082).legal).to_be(true) # C.SLLI shamt[5]
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/hardware/rv64gc/rv64_shared_zca_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV64C shared Zca adapter.
- RV64C shared Zca adapter

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

- `REQ-SSPEC-HARDWARE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ee70cc691ee8bcc2dcd13bdf69d9c3085771c4f64ee625eab37020faa75a3885`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee70cc691ee8bcc2dcd13bdf69d9c3085771c4f64ee625eab37020faa75a3885`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee70cc691ee8bcc2dcd13bdf69d9c3085771c4f64ee625eab37020faa75a3885`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/hardware/rv64gc/rv64_shared_zca_adapter_spec.spl
mirror: doc/06_spec/01_unit/hardware/rv64gc/rv64_shared_zca_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/hardware/rv64gc/rv64_shared_zca_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/hardware/rv64gc/rv64_shared_zca_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/hardware/rv64gc/rv64_shared_zca_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/hardware/rv64gc/rv64_shared_zca_adapter_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the common C.EBREAK, C.NOP, and C.ADDI rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv64gc/rv64_shared_zca_adapter_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'continues to fail closed for the shared all-zero reservation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/hardware/rv64gc/rv64_shared_zca_adapter_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps RV64-only integer forms in the shared RV64 specialization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
