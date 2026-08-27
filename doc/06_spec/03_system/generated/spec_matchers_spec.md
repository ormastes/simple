# spec_matchers_spec

> Tests for BDD matchers in the SPipe framework.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spec_matchers_spec

Tests for BDD matchers in the SPipe framework.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/generated/spec_matchers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for BDD matchers in the SPipe framework.
Validates core matchers, comparison matchers, string matchers,
collection matchers, and negated assertions.

## Scenarios

### BDD Matchers

#### core matchers

#### eq matcher tests equality

- eq matcher tests equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("eq matcher tests equality")
expect 5 to eq 5
expect "hello" to eq "hello"
expect true to eq true
```

</details>

#### be matcher tests identity

- be matcher tests identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("be matcher tests identity")
val x = 5
expect x to be 5
```

</details>

#### be_nil matcher tests None

- be_nil matcher tests None


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("be_nil matcher tests None")
val nothing = nil
expect nothing to be_nil()
```

</details>

#### comparison matchers (numbers)

#### gt (greater than) matcher

- gt (greater than) matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gt (greater than) matcher")
expect 10 to gt 5
expect 100 to gt 50
```

</details>

#### lt (less than) matcher

- lt (less than) matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lt (less than) matcher")
expect 3 to lt 10
expect 1 to lt 100
```

</details>

#### gte (greater than or equal) matcher

- gte (greater than or equal) matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gte (greater than or equal) matcher")
expect 10 to gte 5
expect 5 to gte 5
```

</details>

#### lte (less than or equal) matcher

- lte (less than or equal) matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lte (less than or equal) matcher")
expect 3 to lte 10
expect 5 to lte 5
```

</details>

#### multiple comparisons in one test

- multiple comparisons in one test


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiple comparisons in one test")
expect 5 to gt 0
expect 5 to gte 5
expect 5 to lt 10
expect 5 to lte 5
```

</details>

#### string matchers

#### include matcher for strings

- include matcher for strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("include matcher for strings")
expect "hello world" to include "world"
expect "hello world" to include "hello"
```

</details>

#### start_with matcher

- start_with matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("start_with matcher")
expect "hello world" to start_with "hello"
```

</details>

#### end_with matcher

- end_with matcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("end_with matcher")
expect "hello world" to end_with "world"
```

</details>

#### collection matchers

#### include matcher for arrays

- include matcher for arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("include matcher for arrays")
val arr = [1, 2, 3, 4, 5]
expect arr to include 3
expect arr to include 1
```

</details>

#### negated assertions

#### not_to with eq

- not_to with eq


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("not_to with eq")
expect 5 not_to eq 6
expect "hello" not_to eq "world"
```

</details>

#### not_to with comparison

- not_to with comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("not_to with comparison")
expect 5 not_to gt 10
expect 5 not_to lt 1
```

</details>

#### not_to with include

- not_to with include


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("not_to with include")
expect "hello" not_to include "xyz"
```

</details>

#### complex matcher chains

#### chains multiple matchers on same value

- chains multiple matchers on same value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chains multiple matchers on same value")
expect 10 to gt 5
expect 10 to gte 10
expect 10 to lt 20
expect 10 to lte 10
```

</details>

#### matchers with computed values

- matchers with computed values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matchers with computed values")
val x = 5
val y = 3
val result = x + y
expect result to eq 8
expect result to gt 7
expect result to lt 10
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0b0640e9d8e61a0bad96fe9af8e17de716f6a5b0278cc84117e4c0708d766835`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0b0640e9d8e61a0bad96fe9af8e17de716f6a5b0278cc84117e4c0708d766835`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0b0640e9d8e61a0bad96fe9af8e17de716f6a5b0278cc84117e4c0708d766835`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/generated/spec_matchers_spec.spl
mirror: doc/06_spec/03_system/generated/spec_matchers_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/generated/spec_matchers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/generated/spec_matchers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/generated/spec_matchers_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'eq matcher tests equality' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/spec_matchers_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'be matcher tests identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/spec_matchers_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'be_nil matcher tests None' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
