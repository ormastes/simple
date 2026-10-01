# Format Spec Specification

> Tests covering string format specifiers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Format Spec Specification

## Scenarios

### string format specifiers

#### basic string interpolation works

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- basic string interpolation works
   - Expected: s equals `value is 42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("basic string interpolation works")
val n = 42
val s = "value is {n}"
expect(s).to_equal("value is 42")
```

</details>

#### float interpolation works

- float interpolation works


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("float interpolation works")
val pi = 3.14159
val s = "pi is {pi}"
expect(s).to_contain("3.14")
```

</details>

#### bool interpolation works

- bool interpolation works
   - Expected: s equals `flag=true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bool interpolation works")
val flag = true
val s = "flag={flag}"
expect(s).to_equal("flag=true")
```

</details>

#### text interpolation works

- text interpolation works
   - Expected: greeting equals `Hello, Alice!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("text interpolation works")
val name = "Alice"
val greeting = "Hello, {name}!"
expect(greeting).to_equal("Hello, Alice!")
```

</details>

#### expression interpolation works

- expression interpolation works
   - Expected: s equals `result=10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("expression interpolation works")
val x = 5
val s = "result={x * 2}"
expect(s).to_equal("result=10")
```

</details>

#### multiple interpolations in one string

- multiple interpolations in one string
   - Expected: s equals `3 + 4 = 7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple interpolations in one string")
val a = 3
val b = 4
val s = "{a} + {b} = {a + b}"
expect(s).to_equal("3 + 4 = 7")
```

</details>

#### closing brace escaped with double brace

- closing brace escaped with double brace
   - Expected: s equals `99}remaining`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closing brace escaped with double brace")
val n = 99
val s = "{n}}remaining"
# }} → literal }, result is "99}remaining"
expect(s).to_equal("99}remaining")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/format_spec_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering string format specifiers.
- string format specifiers

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b5997defb608dd360dc978f7fc406ea70351036503e603ec4e633e851e5bc2c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5997defb608dd360dc978f7fc406ea70351036503e603ec4e633e851e5bc2c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5997defb608dd360dc978f7fc406ea70351036503e603ec4e633e851e5bc2c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/format_spec_spec.spl
mirror: doc/06_spec/unit/lib/common/format_spec_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/format_spec_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/format_spec_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/format_spec_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'basic string interpolation works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/format_spec_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'float interpolation works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/format_spec_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bool interpolation works' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
