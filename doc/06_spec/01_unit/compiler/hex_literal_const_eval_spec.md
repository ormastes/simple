# hex_literal_const_eval_spec

> Purpose: Prove that hex literal const-eval.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hex_literal_const_eval_spec

Purpose: Prove that hex literal const-eval.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hex_literal_const_eval_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that hex literal const-eval.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### hex literal const-eval

#### maps lowercase a-f digits

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps lowercase a-f digits
- Verify: maps lowercase a-f digits
   - Expected: 0xca equals `202`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps lowercase a-f digits")
step("Verify: maps lowercase a-f digits")
# @req: REQ-COMP-HEX-LITERAL-CONST-EVAL-001
expect(0xca).to_equal(202)
```

</details>

#### maps a full lowercase word literal

- maps a full lowercase word literal
- Verify: maps a full lowercase word literal
   - Expected: 0xdeadbeef equals `3735928559`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps a full lowercase word literal")
step("Verify: maps a full lowercase word literal")
expect(0xdeadbeef).to_equal(3735928559)
```

</details>

#### maps uppercase A-F digits

- maps uppercase A-F digits
- Verify: maps uppercase A-F digits
   - Expected: 0xDEAD equals `57005`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps uppercase A-F digits")
step("Verify: maps uppercase A-F digits")
expect(0xDEAD).to_equal(57005)
```

</details>

#### maps mixed-case digits

- maps mixed-case digits
- Verify: maps mixed-case digits
   - Expected: 0xAbCdEf equals `11259375`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps mixed-case digits")
step("Verify: maps mixed-case digits")
expect(0xAbCdEf).to_equal(11259375)
```

</details>

#### still maps pure-digit hex

- still maps pure-digit hex
- Verify: still maps pure-digit hex
   - Expected: 0x10 equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still maps pure-digit hex")
step("Verify: still maps pure-digit hex")
expect(0x10).to_equal(16)
```

</details>

#### leaves binary literals intact

- leaves binary literals intact
- Verify: leaves binary literals intact
   - Expected: 0b1010 equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves binary literals intact")
step("Verify: leaves binary literals intact")
expect(0b1010).to_equal(10)
```

</details>

#### leaves octal literals intact

- leaves octal literals intact
- Verify: leaves octal literals intact
   - Expected: 0o17 equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves octal literals intact")
step("Verify: leaves octal literals intact")
expect(0o17).to_equal(15)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-HEX-LITERAL-CONST-EVAL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `18301f0c8d705b8a4946b67876ddf5e91c49180527809eefc19eaf9ebc01a26c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `18301f0c8d705b8a4946b67876ddf5e91c49180527809eefc19eaf9ebc01a26c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `18301f0c8d705b8a4946b67876ddf5e91c49180527809eefc19eaf9ebc01a26c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/hex_literal_const_eval_spec.spl
mirror: doc/06_spec/01_unit/compiler/hex_literal_const_eval_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hex_literal_const_eval_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hex_literal_const_eval_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hex_literal_const_eval_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hex_literal_const_eval_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps lowercase a-f digits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hex_literal_const_eval_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps a full lowercase word literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hex_literal_const_eval_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps uppercase A-F digits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
