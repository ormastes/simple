# Bare Trailing Neg Literal Specification

> Tests covering parser — bare trailing negative literal, inline-if followed by a bare `-1` tail expression, the real config_core site (_cfg_find_char shape), the shipped caller that depends on the sentinel.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bare Trailing Neg Literal Specification

## Scenarios

### parser — bare trailing negative literal

### inline-if followed by a bare `-1` tail expression

#### returns the inline-if value on the taken path, not value-minus-one

- returns the inline-if value on the taken path, not value-minus-one
- call the fixture with the inline-if branch taken
   - Expected: rank(x: true) equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the inline-if value on the taken path, not value-minus-one")
step("call the fixture with the inline-if branch taken")
expect(rank(x: true)).to_equal(9)
```

</details>

#### returns the sentinel -1 on the fallthrough path, not nil

- returns the sentinel -1 on the fallthrough path, not nil
- call the fixture with the inline-if branch not taken
   - Expected: rank(x: false) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the sentinel -1 on the fallthrough path, not nil")
step("call the fixture with the inline-if branch not taken")
expect(rank(x: false)).to_equal(-1)
```

</details>

#### keeps a compound trailing expression separate from the previous line

- keeps a compound trailing expression separate from the previous line
- `-1 - 1` must evaluate as -2, never fold into `return 9`
   - Expected: rank_compound(x: true) equals `9`
   - Expected: rank_compound(x: false) equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps a compound trailing expression separate from the previous line")
step("`-1 - 1` must evaluate as -2, never fold into `return 9`")
expect(rank_compound(x: true)).to_equal(9)
expect(rank_compound(x: false)).to_equal(-2)
```

</details>

### the real config_core site (_cfg_find_char shape)

#### returns the index on a hit

- returns the index on a hit
- search for a character that is present
   - Expected: find_char(s: "abc", ch: "b") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the index on a hit")
step("search for a character that is present")
expect(find_char(s: "abc", ch: "b")).to_equal(1)
```

</details>

#### returns -1 on a miss instead of a folded or nil value

- returns -1 on a miss instead of a folded or nil value
- search for a character that is absent
   - Expected: find_char(s: "abc", ch: "z") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns -1 on a miss instead of a folded or nil value")
step("search for a character that is absent")
expect(find_char(s: "abc", ch: "z")).to_equal(-1)
```

</details>

### the shipped caller that depends on the sentinel

#### leaves a value with no inline comment untouched

- leaves a value with no inline comment untouched
- config_strip_inline_comment relies on the -1 miss sentinel
   - Expected: config_strip_inline_comment("true") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves a value with no inline comment untouched")
step("config_strip_inline_comment relies on the -1 miss sentinel")
expect(config_strip_inline_comment("true")).to_equal("true")
```

</details>

#### strips an inline comment when the sentinel search hits

- strips an inline comment when the sentinel search hits
- a `#` present must be found, not reported as a miss
   - Expected: config_strip_inline_comment("true   # note") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("strips an inline comment when the sentinel search hits")
step("a `#` present must be found, not reported as a miss")
expect(config_strip_inline_comment("true   # note")).to_equal("true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/config_core/bare_trailing_neg_literal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering parser — bare trailing negative literal, inline-if followed by a bare `-1` tail expression, the real config_core site (_cfg_find_char shape), the shipped caller that depends on the sentinel.
- parser — bare trailing negative literal
- inline-if followed by a bare `-1` tail expression
- the real config_core site (_cfg_find_char shape)
- the shipped caller that depends on the sentinel

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `717c45bb1ec45c30e3c507a8f951fb043565625ceff6c6501089b61fc7a9bc24`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `717c45bb1ec45c30e3c507a8f951fb043565625ceff6c6501089b61fc7a9bc24`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `717c45bb1ec45c30e3c507a8f951fb043565625ceff6c6501089b61fc7a9bc24`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/config_core/bare_trailing_neg_literal_spec.spl
mirror: doc/06_spec/01_unit/lib/common/config_core/bare_trailing_neg_literal_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/config_core/bare_trailing_neg_literal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/config_core/bare_trailing_neg_literal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/config_core/bare_trailing_neg_literal_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/config_core/bare_trailing_neg_literal_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the inline-if value on the taken path, not value-minus-one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/config_core/bare_trailing_neg_literal_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the sentinel -1 on the fallthrough path, not nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/config_core/bare_trailing_neg_literal_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a compound trailing expression separate from the previous line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
