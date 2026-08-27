# native_build_digit_accumulator_class_spec

> Purpose: Prove that digit-accumulator character-code contamination (defect class).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_build_digit_accumulator_class_spec

Purpose: Prove that digit-accumulator character-code contamination (defect class).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/native_build_digit_accumulator_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that digit-accumulator character-code contamination (defect class).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### digit-accumulator character-code contamination (defect class)

#### documents the primitive that makes this class possible

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- documents the primitive that makes this class possible
- Verify: documents the primitive that makes this class possible
   - Expected: int("0") equals `48`
   - Expected: int("9") equals `57`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("documents the primitive that makes this class possible")
step("Verify: documents the primitive that makes this class possible")
# @req: REQ-APP-CLI-001
# int() on a one-char text is a CODE, not a value. Any hand-rolled
# parser in this file that forgets this is the same bug again.
expect(int("0")).to_equal(48)
expect(int("9")).to_equal(57)
```

</details>

#### gives every digit 0-9 its own value in isolation

- gives every digit 0-9 its own value in isolation
- Verify: gives every digit 0-9 its own value in isolation
   - Expected: native_build_parse_secs("0") equals `0`
   - Expected: native_build_parse_secs("1") equals `1`
   - Expected: native_build_parse_secs("2") equals `2`
   - Expected: native_build_parse_secs("3") equals `3`
   - Expected: native_build_parse_secs("4") equals `4`
   - Expected: native_build_parse_secs("5") equals `5`
   - Expected: native_build_parse_secs("6") equals `6`
   - Expected: native_build_parse_secs("7") equals `7`
   - Expected: native_build_parse_secs("8") equals `8`
   - Expected: native_build_parse_secs("9") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("gives every digit 0-9 its own value in isolation")
step("Verify: gives every digit 0-9 its own value in isolation")
expect(native_build_parse_secs("0")).to_equal(0)
expect(native_build_parse_secs("1")).to_equal(1)
expect(native_build_parse_secs("2")).to_equal(2)
expect(native_build_parse_secs("3")).to_equal(3)
expect(native_build_parse_secs("4")).to_equal(4)
expect(native_build_parse_secs("5")).to_equal(5)
expect(native_build_parse_secs("6")).to_equal(6)
expect(native_build_parse_secs("7")).to_equal(7)
expect(native_build_parse_secs("8")).to_equal(8)
expect(native_build_parse_secs("9")).to_equal(9)
```

</details>

#### is position-independent: the same digits in any column carry no code offset

- is position-independent: the same digits in any column carry no code offset
- Verify: is position-independent: the same digits in any column carry no code offset
   - Expected: native_build_parse_secs("10") equals `10`
   - Expected: native_build_parse_secs("100") equals `100`
   - Expected: native_build_parse_secs("1000") equals `1000`
   - Expected: native_build_parse_secs("12345") equals `12345`
   - Expected: native_build_parse_secs("999999") equals `999999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is position-independent: the same digits in any column carry no code offset")
step("Verify: is position-independent: the same digits in any column carry no code offset")
expect(native_build_parse_secs("10")).to_equal(10)
expect(native_build_parse_secs("100")).to_equal(100)
expect(native_build_parse_secs("1000")).to_equal(1000)
expect(native_build_parse_secs("12345")).to_equal(12345)
expect(native_build_parse_secs("999999")).to_equal(999999)
```

</details>

#### treats leading zeros as zeros, not as 48s

- treats leading zeros as zeros, not as 48s
- Verify: treats leading zeros as zeros, not as 48s
   - Expected: native_build_parse_secs("007") equals `7`
   - Expected: native_build_parse_secs("0090") equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("treats leading zeros as zeros, not as 48s")
step("Verify: treats leading zeros as zeros, not as 48s")
expect(native_build_parse_secs("007")).to_equal(7)
expect(native_build_parse_secs("0090")).to_equal(90)
```

</details>

#### never returns a budget larger than the digits could justify

- never returns a budget larger than the digits could justify
- Verify: never returns a budget larger than the digits could justify
   - Expected: native_build_parse_secs("9") <= 9 is true
   - Expected: native_build_parse_secs("99") <= 99 is true
   - Expected: native_build_parse_secs("999") <= 999 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("never returns a budget larger than the digits could justify")
step("Verify: never returns a budget larger than the digits could justify")
# A code-contaminated accumulator inflates by ~5x per column; this is
# the cheap invariant that catches the whole class regardless of the
# specific arithmetic slip.
expect(native_build_parse_secs("9") <= 9).to_equal(true)
expect(native_build_parse_secs("99") <= 99).to_equal(true)
expect(native_build_parse_secs("999") <= 999).to_equal(true)
```

</details>

#### propagates the corrected value all the way to the millisecond budget

- propagates the corrected value all the way to the millisecond budget
- Verify: propagates the corrected value all the way to the millisecond budget
   - Expected: native_build_timeout_ms(["--timeout", "1"]) equals `1000`
   - Expected: native_build_timeout_ms(["--timeout=99"]) equals `99000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("propagates the corrected value all the way to the millisecond budget")
step("Verify: propagates the corrected value all the way to the millisecond budget")
expect(native_build_timeout_ms(["--timeout", "1"])).to_equal(1000)
expect(native_build_timeout_ms(["--timeout=99"])).to_equal(99000)
```

</details>

#### falls back to the default budget rather than a garbage one on bad input

- falls back to the default budget rather than a garbage one on bad input
- Verify: falls back to the default budget rather than a garbage one on bad input
   - Expected: native_build_timeout_ms(["--timeout", "nope"]) > 0 is true
   - Expected: native_build_timeout_ms([]) > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("falls back to the default budget rather than a garbage one on bad input")
step("Verify: falls back to the default budget rather than a garbage one on bad input")
# -1 must not become a live budget; the caller must see the default.
expect(native_build_timeout_ms(["--timeout", "nope"]) > 0).to_equal(true)
expect(native_build_timeout_ms([]) > 0).to_equal(true)
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

- `REQ-SSPEC-APP`
- `REQ-APP-CLI-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ff4f0d22ee1d6e15c600d875524f60127eb2bdee472c4c6a4fa59318d7331688`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ff4f0d22ee1d6e15c600d875524f60127eb2bdee472c4c6a4fa59318d7331688`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ff4f0d22ee1d6e15c600d875524f60127eb2bdee472c4c6a4fa59318d7331688`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/cli/native_build_digit_accumulator_class_spec.spl
mirror: doc/06_spec/01_unit/app/cli/native_build_digit_accumulator_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/cli/native_build_digit_accumulator_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/cli/native_build_digit_accumulator_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/cli/native_build_digit_accumulator_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/cli/native_build_digit_accumulator_class_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents the primitive that makes this class possible' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/native_build_digit_accumulator_class_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives every digit 0-9 its own value in isolation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/cli/native_build_digit_accumulator_class_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is position-independent: the same digits in any column carry no code offset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
