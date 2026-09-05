# Result under the forced-interpret test lane Specification

> `bin/simple test` forces SIMPLE_EXECUTION_MODE=interpret, and two lanes independently found Result-wrapped APIs untestable there: "variable `Result` not found" (direct) or "unknown class Result" (imported module, e.g. bencode_decode_value) because the builtin Option/Result enums were never registered in the interpreter's enum registry (user enums were); SIMPLE_BOOTSTRAP=1 textual `strip_optionals` preprocessor deleting the try-operator from valid sources before parse (now fallback-only).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Result under the forced-interpret test lane Specification

`bin/simple test` forces SIMPLE_EXECUTION_MODE=interpret, and two lanes independently found Result-wrapped APIs untestable there: "variable `Result` not found" (direct) or "unknown class Result" (imported module, e.g. bencode_decode_value) because the builtin Option/Result enums were never registered in the interpreter's enum registry (user enums were); SIMPLE_BOOTSTRAP=1 textual `strip_optionals` preprocessor deleting the try-operator from valid sources before parse (now fallback-only).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-RESULT-LANE-001 |
| Category | Runtime |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/08_tracking/bug/test_harness_execution_divergence_2026-07-29.md |
| Source | `test/01_unit/bugs/result_interpret_lane_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`bin/simple test` forces SIMPLE_EXECUTION_MODE=interpret, and two lanes
independently found Result-wrapped APIs untestable there:
- qualified construction `Result.Ok(x)` / `Result.Err(e)` failed with
  "variable `Result` not found" (direct) or "unknown class Result"
  (imported module, e.g. bencode_decode_value) because the builtin
  Option/Result enums were never registered in the interpreter's enum
  registry (user enums were);
- the `?` operator appeared broken in BOTH engines, but that was the
  SIMPLE_BOOTSTRAP=1 textual `strip_optionals` preprocessor deleting the
  try-operator from valid sources before parse (now fallback-only).

This spec runs under the forced-interpret lane by construction and pins
every consumption form, using bencode_decode_value as the integration
proof for the imported-module path.

## Scenarios

### Result under the forced-interpret test lane

#### bare construction and match

#### matches Ok with its payload

- matches Ok with its payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("matches Ok with its payload")
match half(10):
    case Ok(v): expect(v).to_equal(5)
    case Err(e): expect(e).to_equal("UNREACHED")
```

</details>

#### matches Err with its payload

- matches Err with its payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("matches Err with its payload")
match half(7):
    case Ok(v): expect(v).to_equal(-1)
    case Err(e): expect(e).to_equal("odd: 7")
```

</details>

#### QUALIFIED construction (the reported failure)

#### constructs via Result.Ok

- constructs via Result.Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("constructs via Result.Ok")
match qual(21):
    case Ok(v): expect(v).to_equal(42)
    case Err(e): expect(e).to_equal("UNREACHED")
```

</details>

#### constructs via Result.Err

- constructs via Result.Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("constructs via Result.Err")
match qual(-1):
    case Ok(v): expect(v).to_equal(-1)
    case Err(e): expect(e).to_equal("neg")
```

</details>

#### constructs via Option.Some and Option.None

- constructs via Option.Some and Option.None


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("constructs via Option.Some and Option.None")
match opt_qual(9):
    case Some(v): expect(v).to_equal(9)
    case _: expect(true).to_equal(false)
match opt_qual(-9):
    case Some(v): expect(v).to_equal(-1)
    case _: expect(1).to_equal(1)
```

</details>

#### question-mark operator

#### unwraps Ok through ?

- unwraps Ok through ?


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("unwraps Ok through ?")
match via_try(10):
    case Ok(v): expect(v).to_equal(105)
    case Err(e): expect(e).to_equal("UNREACHED")
```

</details>

#### propagates Err through ?

- propagates Err through ?


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("propagates Err through ?")
match via_try(7):
    case Ok(v): expect(v).to_equal(-1)
    case Err(e): expect(e).to_equal("odd: 7")
```

</details>

#### method consumption

#### is_ok and unwrap agree with match

- is_ok and unwrap agree with match
   - Expected: r.unwrap() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("is_ok and unwrap agree with match")
val r = half(4)
expect(r.is_ok()).to_be_true()
expect(r.unwrap()).to_equal(2)
```

</details>

#### imported-module integration (bencode)

#### bencode_decode_value's Result API is exercisable

- bencode_decode_value's Result API is exercisable


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("bencode_decode_value's Result API is exercisable")
# This exact call failed with "unknown class Result" under the
# test lane before the registry fix.
match bencode_decode_value("i42e"):
    case Ok(v): expect(1).to_equal(1)
    case Err(e): expect(1).to_equal(-1)
```

</details>

#### reports trailing data as Err

- reports trailing data as Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("reports trailing data as Err")
match bencode_decode_value("i42eXX"):
    case Ok(v): expect(1).to_equal(-1)
    case Err(e): expect(1).to_equal(1)
```

</details>

#### vacuity probe

#### executes assertions in this file

- executes assertions in this file
   - Expected: half(8).unwrap() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("executes assertions in this file")
expect(half(8).unwrap()).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** `doc/08_tracking/bug/test_harness_execution_divergence_2026-07-29.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BUGS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `af1486df31fbac1c200187922e6a2befb5a945ec3facc6dae4aff533698cabd6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `af1486df31fbac1c200187922e6a2befb5a945ec3facc6dae4aff533698cabd6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `af1486df31fbac1c200187922e6a2befb5a945ec3facc6dae4aff533698cabd6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/bugs/result_interpret_lane_spec.spl
mirror: doc/06_spec/01_unit/bugs/result_interpret_lane_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/bugs/result_interpret_lane_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/bugs/result_interpret_lane_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/bugs/result_interpret_lane_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/bugs/result_interpret_lane_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches Ok with its payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/result_interpret_lane_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches Err with its payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/result_interpret_lane_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs via Result.Ok' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
