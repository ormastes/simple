# arm_target_spec

> Purpose: Prove that ArmCortexMTarget Cortex-M7.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# arm_target_spec

Purpose: Prove that ArmCortexMTarget Cortex-M7.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/debug/remote/arm_target_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that ArmCortexMTarget Cortex-M7.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### ArmCortexMTarget Cortex-M7

#### has correct name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has correct name
- Verify: has correct name
   - Expected: t.name() equals `ARM Cortex-M7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct name")
step("Verify: has correct name")
# @req: REQ-APP-DEBUG-001
val t = ArmCortexMTarget.cortex_m7()
expect(t.name()).to_equal("ARM Cortex-M7")
```

</details>

#### has correct core name

- has correct core name
- Verify: has correct core name
   - Expected: t.core_name() equals `Cortex-M7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct core name")
step("Verify: has correct core name")
val t = ArmCortexMTarget.cortex_m7()
expect(t.core_name()).to_equal("Cortex-M7")
```

</details>

#### has 21 registers

- has 21 registers
- Verify: has 21 registers
   - Expected: t.register_count() equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has 21 registers")
step("Verify: has 21 registers")
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_count()).to_equal(21)  # oracle: 21 — named expected value from the requirement
```

</details>

#### has 6 HW breakpoints for M7

- has 6 HW breakpoints for M7
- Verify: has 6 HW breakpoints for M7
   - Expected: t.hw_breakpoint_count() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has 6 HW breakpoints for M7")
step("Verify: has 6 HW breakpoints for M7")
val t = ArmCortexMTarget.cortex_m7()
expect(t.hw_breakpoint_count()).to_equal(6)  # oracle: 6 — named expected value from the requirement
```

</details>

#### has 4 HW watchpoints

- has 4 HW watchpoints
- Verify: has 4 HW watchpoints
   - Expected: t.hw_watchpoint_count() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has 4 HW watchpoints")
step("Verify: has 4 HW watchpoints")
val t = ArmCortexMTarget.cortex_m7()
expect(t.hw_watchpoint_count()).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

### ArmCortexMTarget Cortex-M4

#### has correct name

- has correct name
- Verify: has correct name
   - Expected: t.name() equals `ARM Cortex-M4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct name")
step("Verify: has correct name")
val t = ArmCortexMTarget.cortex_m4()
expect(t.name()).to_equal("ARM Cortex-M4")
```

</details>

#### has 4 HW breakpoints for M4

- has 4 HW breakpoints for M4
- Verify: has 4 HW breakpoints for M4
   - Expected: t.hw_breakpoint_count() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has 4 HW breakpoints for M4")
step("Verify: has 4 HW breakpoints for M4")
val t = ArmCortexMTarget.cortex_m4()
expect(t.hw_breakpoint_count()).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

### ArmCortexMTarget register lookups

#### r0 is index 0

- r0 is index 0
- Verify: r0 is index 0
   - Expected: t.register_index("r0") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("r0 is index 0")
step("Verify: r0 is index 0")
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_index("r0")).to_equal(0)
```

</details>

#### pc is index 15

- pc is index 15
- Verify: pc is index 15
   - Expected: t.register_index("pc") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pc is index 15")
step("Verify: pc is index 15")
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_index("pc")).to_equal(15)
```

</details>

#### sp is index 13

- sp is index 13
- Verify: sp is index 13
   - Expected: t.register_index("sp") equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sp is index 13")
step("Verify: sp is index 13")
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_index("sp")).to_equal(13)
```

</details>

#### xPSR is index 16

- xPSR is index 16
- Verify: xPSR is index 16
   - Expected: t.register_index("xPSR") equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("xPSR is index 16")
step("Verify: xPSR is index 16")
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_index("xPSR")).to_equal(16)
```

</details>

#### unknown register returns -1

- unknown register returns -1
- Verify: unknown register returns -1
   - Expected: t.register_index("nonexistent") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown register returns -1")
step("Verify: unknown register returns -1")
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_index("nonexistent")).to_equal(-1)
```

</details>

#### register_name at 0 is r0

- register_name at 0 is r0
- Verify: register_name at 0 is r0
   - Expected: t.register_name(0) equals `r0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("register_name at 0 is r0")
step("Verify: register_name at 0 is r0")
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_name(0)).to_equal("r0")
```

</details>

#### register_name out of bounds is unknown

- register_name out of bounds is unknown
- Verify: register_name out of bounds is unknown
   - Expected: t.register_name(100) equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("register_name out of bounds is unknown")
step("Verify: register_name out of bounds is unknown")
val t = ArmCortexMTarget.cortex_m7()
expect(t.register_name(100)).to_equal("unknown")
```

</details>

### ArmCortexMTarget breakpoint

#### thumb BKPT instruction is 0x00 0xBE

- thumb BKPT instruction is 0x00 0xBE
- Verify: thumb BKPT instruction is 0x00 0xBE
   - Expected: bkpt.len() equals `2`
   - Expected: bkpt[0] equals `0`
   - Expected: bkpt[1] equals `190`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("thumb BKPT instruction is 0x00 0xBE")
step("Verify: thumb BKPT instruction is 0x00 0xBE")
val t = ArmCortexMTarget.cortex_m7()
val bkpt = t.breakpoint_instruction()
expect(bkpt.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(bkpt[0]).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(bkpt[1]).to_equal(190)  # oracle: 190 — named expected value from the requirement
```

</details>

#### word size is 4

- word size is 4
- Verify: word size is 4
   - Expected: t.word_size() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("word size is 4")
step("Verify: word size is 4")
val t = ArmCortexMTarget.cortex_m7()
expect(t.word_size()).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### supports single step

- supports single step
- Verify: supports single step
   - Expected: t.supports_single_step() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports single step")
step("Verify: supports single step")
val t = ArmCortexMTarget.cortex_m7()
expect(t.supports_single_step()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-DEBUG-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `030e6409fdc5d1bddf06bb89d213b15e74e094d43b39530773a7006cc8777677`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `030e6409fdc5d1bddf06bb89d213b15e74e094d43b39530773a7006cc8777677`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `030e6409fdc5d1bddf06bb89d213b15e74e094d43b39530773a7006cc8777677`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/debug/remote/arm_target_spec.spl
mirror: doc/06_spec/unit/app/debug/remote/arm_target_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/debug/remote/arm_target_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/debug/remote/arm_target_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/debug/remote/arm_target_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/debug/remote/arm_target_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/arm_target_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct core name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/arm_target_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has 21 registers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
