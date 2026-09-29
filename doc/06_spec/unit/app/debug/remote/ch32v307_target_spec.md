# Ch32v307 Target Specification

> Tests covering Ch32v307Target defaults.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ch32v307 Target Specification

## Scenarios

### Ch32v307Target defaults

#### has correct name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has correct name
   - Expected: t.name() equals `CH32V307 (RV32IMAC+F)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct name")
val t = Ch32v307Target.default()
expect(t.name()).to_equal("CH32V307 (RV32IMAC+F)")
```

</details>

#### has correct WCH-Link serial

- has correct WCH-Link serial
   - Expected: t.wlink_serial equals `711A8F06F64D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct WCH-Link serial")
val t = Ch32v307Target.default()
expect(t.wlink_serial).to_equal("711A8F06F64D")
```

</details>

#### has correct chip ID

- has correct chip ID
   - Expected: t.chip_id equals `0x30700568`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct chip ID")
val t = Ch32v307Target.default()
expect(t.chip_id).to_equal("0x30700568")
```

</details>

#### has correct flash base and size

- has correct flash base and size
   - Expected: t.flash_base equals `0x08000000`
   - Expected: t.flash_size equals `294912`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct flash base and size")
val t = Ch32v307Target.default()
expect(t.flash_base).to_equal(0x08000000)
expect(t.flash_size).to_equal(294912)
```

</details>

#### has correct RAM base and size

- has correct RAM base and size
   - Expected: t.ram_base equals `0x20000000`
   - Expected: t.ram_size equals `32768`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct RAM base and size")
val t = Ch32v307Target.default()
expect(t.ram_base).to_equal(0x20000000)
expect(t.ram_size).to_equal(32768)
```

</details>

#### has correct ISA

- has correct ISA
   - Expected: t.isa equals `RV32ACFIMUX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct ISA")
val t = Ch32v307Target.default()
expect(t.isa).to_equal("RV32ACFIMUX")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/debug/remote/ch32v307_target_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Ch32v307Target defaults.
- Ch32v307Target defaults

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cb702d0c3e7417725252a8a45f6b24b87fce114bcd18bb40c44f3cf427f6a44f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cb702d0c3e7417725252a8a45f6b24b87fce114bcd18bb40c44f3cf427f6a44f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cb702d0c3e7417725252a8a45f6b24b87fce114bcd18bb40c44f3cf427f6a44f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/debug/remote/ch32v307_target_spec.spl
mirror: doc/06_spec/unit/app/debug/remote/ch32v307_target_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/debug/remote/ch32v307_target_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/debug/remote/ch32v307_target_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/debug/remote/ch32v307_target_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/debug/remote/ch32v307_target_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/ch32v307_target_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct WCH-Link serial' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/ch32v307_target_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct chip ID' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
