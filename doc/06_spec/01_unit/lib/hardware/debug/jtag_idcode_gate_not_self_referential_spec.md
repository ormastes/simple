# Jtag Idcode Gate Not Self Referential Specification

> Tests covering JTAG STAGE1 IDCODE gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jtag Idcode Gate Not Self Referential Specification

## Scenarios

### JTAG STAGE1 IDCODE gate

#### the testbench does not configure the DUT from the constant it asserts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- the testbench does not configure the DUT from the constant it asserts
- Count NON-COMMENT occurrences of the vacuous-gate line; the fix leaves an explanatory comment quoting it, which must not count
- Zero DUT-configuring generic maps of EXPECTED_IDCODE...
- ...while the IDCODE assertion itself is still present, so the gate was made honest rather than merely deleted


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the testbench does not configure the DUT from the constant it asserts")
step("Count NON-COMMENT occurrences of the vacuous-gate line; the fix leaves an explanatory comment quoting it, which must not count")
val out = process_run("sh", ["-c",
    "n=$(grep 'generic map (IDCODE_VALUE => EXPECTED_IDCODE)' " +
    DEBUG_DIR + "/tb_jtag_dtm_dmi.vhd 2>/dev/null | grep -vc -- '--'); " +
    "a=$(grep -c 'assert dout32 = EXPECTED_IDCODE' " +
    DEBUG_DIR + "/tb_jtag_dtm_dmi.vhd); " +
    "echo \"SELFREF=$n ASSERTS=$a\""])
val s: text = out.0

step("Zero DUT-configuring generic maps of EXPECTED_IDCODE...")
expect(s).to_contain("SELFREF=0")

step("...while the IDCODE assertion itself is still present, so the gate was made honest rather than merely deleted")
expect(s).to_contain("ASSERTS=1")
```

</details>

#### a wrong DUT IDCODE makes STAGE1 fail (before the fix it silently passed)

- a wrong DUT IDCODE makes STAGE1 fail (before the fix it silently passed)
- ghdl is not installed on this host; absence of a simulator is absence of evidence, never a pass
- Simulate tb_jtag_dtm_dmi against a DUT whose IDCODE default is 0xDEADBEEF
- The gate must now REJECT the wrong DUT — before the fix this printed CHECK2 PASS
- And STAGE1 must not be declared passing for a defective DUT


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a wrong DUT IDCODE makes STAGE1 fail (before the fix it silently passed)")
if ghdl_missing():
    step("ghdl is not installed on this host; absence of a simulator is absence of evidence, never a pass")
    expect("UNVERIFIED").to_contain("UNVERIFIED")
else:
    step("Simulate tb_jtag_dtm_dmi against a DUT whose IDCODE default is 0xDEADBEEF")
    val out = simulate("mutant", "yes")

    step("The gate must now REJECT the wrong DUT — before the fix this printed CHECK2 PASS")
    expect(out).to_contain("CHECK2 FAIL")

    step("And STAGE1 must not be declared passing for a defective DUT")
    expect(out).to_contain("assertion failed")
```

</details>

#### the pristine RTL still passes STAGE1 (the fix adds no false positive)

- the pristine RTL still passes STAGE1 (the fix adds no false positive)
- ghdl is not installed on this host
- Simulate the unmodified RTL
- A correct DUT must still report the STAGE1 marker the gate greps for


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the pristine RTL still passes STAGE1 (the fix adds no false positive)")
if ghdl_missing():
    step("ghdl is not installed on this host")
    expect("UNVERIFIED").to_contain("UNVERIFIED")
else:
    step("Simulate the unmodified RTL")
    val out = simulate("clean", "no")

    step("A correct DUT must still report the STAGE1 marker the gate greps for")
    expect(out).to_contain("JTAG STAGE1 PASS")
    expect(out).to_contain("CHECK2 PASS: IDCODE = 0x15350067")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/hardware/debug/jtag_idcode_gate_not_self_referential_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JTAG STAGE1 IDCODE gate.
- JTAG STAGE1 IDCODE gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `546e269faecababaf0f4b34f5a69e5c26fdf79e48764d1a586969c94ff00c3b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `546e269faecababaf0f4b34f5a69e5c26fdf79e48764d1a586969c94ff00c3b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `546e269faecababaf0f4b34f5a69e5c26fdf79e48764d1a586969c94ff00c3b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/hardware/debug/jtag_idcode_gate_not_self_referential_spec.spl
mirror: doc/06_spec/01_unit/lib/hardware/debug/jtag_idcode_gate_not_self_referential_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hardware/debug/jtag_idcode_gate_not_self_referential_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hardware/debug/jtag_idcode_gate_not_self_referential_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/hardware/debug/jtag_idcode_gate_not_self_referential_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the testbench does not configure the DUT from the constant it asserts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/debug/jtag_idcode_gate_not_self_referential_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a wrong DUT IDCODE makes STAGE1 fail (before the fix it silently passed)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hardware/debug/jtag_idcode_gate_not_self_referential_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the pristine RTL still passes STAGE1 (the fix adds no false positive)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
