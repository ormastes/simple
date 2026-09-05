# @req REQ-SSPEC-UNIT

> expect(embedded_sandbox_section_text_valid(lowering)).to_equal(true)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @req REQ-SSPEC-UNIT

expect(embedded_sandbox_section_text_valid(lowering)).to_equal(true)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/security/sandbox_boot_apply_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

expect(embedded_sandbox_section_text_valid(lowering)).to_equal(true)
        expect(embedded_sandbox_lowering_sdn_from_section(4096, 8192, lowering)).to_equal(lowering)

    it "maps lowered region size and permissions to ARM MPU RASR bits":
        step("maps lowered region size and permissions to ARM MPU RASR bits")
        expect(arm_mpu_region_size_encoding(4096)).to_equal(11)
        expect(arm_mpu_access_permission_bits("rw")).to_equal(3 << 24)
        expect((arm_mpu_rasr_value(4096, "rw") & ARM_MPU_RASR_XN) != 0).to_equal(true)
        expect((arm_mpu_rasr_value(4096, "rx") & ARM_MPU_RASR_XN)).to_equal(0)

    it "builds concrete ARM MPU MMIO writes from sandbox lowering":
        step("builds concrete ARM MPU MMIO writes from sandbox lowering")
        val lowering = """
sandbox_lowering:
  pmp_region|2147483648|4096|rw|locked

## Scenarios

### sandbox boot apply metadata and ARM MPU planning

#### fails closed for missing embedded sandbox section bounds

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fails closed for missing embedded sandbox section bounds
   - Expected: embedded_sandbox_section_bounds_valid(0, 4096) is false
   - Expected: embedded_sandbox_lowering_sdn_from_section(4096, 4096, "sandbox_lowering:") equals ``
   - Expected: embedded_sandbox_lowering_sdn_from_raw_bounds(0, 0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed for missing embedded sandbox section bounds")
expect(embedded_sandbox_section_bounds_valid(0, 4096)).to_equal(false)
expect(embedded_sandbox_lowering_sdn_from_section(4096, 4096, "sandbox_lowering:")).to_equal("")
expect(embedded_sandbox_lowering_sdn_from_raw_bounds(0, 0)).to_equal("")
```

</details>

#### accepts bounded generated sandbox lowering section text

- accepts bounded generated sandbox lowering section text


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts bounded generated sandbox lowering section text")
val lowering = """
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

- Canonical SPipe generation for source `3aebe3e1f1d9211a47f10e23bebeeb0f895575b308c772289dedd2be35f482b2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3aebe3e1f1d9211a47f10e23bebeeb0f895575b308c772289dedd2be35f482b2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3aebe3e1f1d9211a47f10e23bebeeb0f895575b308c772289dedd2be35f482b2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/os/kernel/security/sandbox_boot_apply_spec.spl
mirror: doc/06_spec/unit/os/kernel/security/sandbox_boot_apply_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/security/sandbox_boot_apply_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/security/sandbox_boot_apply_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/security/sandbox_boot_apply_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/security/sandbox_boot_apply_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed for missing embedded sandbox section bounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/security/sandbox_boot_apply_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts bounded generated sandbox lowering section text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/security/sandbox_boot_apply_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps lowered region size and permissions to ARM MPU RASR bits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
