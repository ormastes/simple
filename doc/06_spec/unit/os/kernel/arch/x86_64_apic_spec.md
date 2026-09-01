# x86_64 Local APIC ICR Encoding Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86_64 Local APIC ICR Encoding Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/arch/x86_64_apic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### x86_64 APIC ICR encoding

#### encodes physical destination APIC id in ICR high

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- encodes physical destination APIC id in ICR high
   - Expected: apic_icr_high_for_apic_id(0x12u32) equals `0x12000000u32`
   - Expected: apic_icr_high_for_apic_id(0x123u32) equals `0x23000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes physical destination APIC id in ICR high")
expect(apic_icr_high_for_apic_id(0x12u32)).to_equal(0x12000000u32)
expect(apic_icr_high_for_apic_id(0x123u32)).to_equal(0x23000000u32)
```

</details>

#### encodes fixed-vector IPIs

- encodes fixed-vector IPIs
   - Expected: apic_icr_low_fixed(0x41u8) equals `0x41u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes fixed-vector IPIs")
expect(apic_icr_low_fixed(0x41u8)).to_equal(0x41u32)
```

</details>

#### encodes INIT assert for AP startup

- encodes INIT assert for AP startup
   - Expected: apic_icr_low_init() equals `0xC500u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes INIT assert for AP startup")
expect(apic_icr_low_init()).to_equal(0xC500u32)
```

</details>

#### encodes Startup IPI vector

- encodes Startup IPI vector
   - Expected: apic_icr_low_sipi(0x08u8) equals `0x608u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes Startup IPI vector")
expect(apic_icr_low_sipi(0x08u8)).to_equal(0x608u32)
```

</details>

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c2bd9b8d6a1d1fe62a1b133524156ea32f17a158d2e4e9c55c3255f6b88ba54d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c2bd9b8d6a1d1fe62a1b133524156ea32f17a158d2e4e9c55c3255f6b88ba54d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c2bd9b8d6a1d1fe62a1b133524156ea32f17a158d2e4e9c55c3255f6b88ba54d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/arch/x86_64_apic_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/x86_64_apic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/x86_64_apic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/x86_64_apic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/x86_64_apic_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes physical destination APIC id in ICR high' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/x86_64_apic_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes fixed-vector IPIs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/x86_64_apic_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes INIT assert for AP startup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
