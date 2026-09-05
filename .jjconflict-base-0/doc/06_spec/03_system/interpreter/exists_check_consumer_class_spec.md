# Exists Check Consumer Class Specification

> Tests covering ExistsCheck consumer class - falsy payloads across consumers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Exists Check Consumer Class Specification

## Scenarios

### ExistsCheck consumer class - falsy payloads across consumers

#### and consumer treats Some(0) as present

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- and consumer treats Some(0) as present
   - Expected: and_consumer(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("and consumer treats Some(0) as present")
expect(and_consumer(0)).to_equal(true)
```

</details>

#### and consumer treats nil as absent

- and consumer treats nil as absent
   - Expected: and_consumer(nil) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("and consumer treats nil as absent")
expect(and_consumer(nil)).to_equal(false)
```

</details>

#### or consumer treats Some(0) as present

- or consumer treats Some(0) as present
   - Expected: or_consumer(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("or consumer treats Some(0) as present")
expect(or_consumer(0)).to_equal(true)
```

</details>

#### or consumer treats nil as absent

- or consumer treats nil as absent
   - Expected: or_consumer(nil) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("or consumer treats nil as absent")
expect(or_consumer(nil)).to_equal(false)
```

</details>

#### not consumer treats Some(0) as present

- not consumer treats Some(0) as present
   - Expected: not_consumer(0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("not consumer treats Some(0) as present")
expect(not_consumer(0)).to_equal(false)
```

</details>

#### not consumer treats nil as absent

- not consumer treats nil as absent
   - Expected: not_consumer(nil) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("not consumer treats nil as absent")
expect(not_consumer(nil)).to_equal(true)
```

</details>

#### Some(false) is present

- Some(false) is present
   - Expected: bool_payload(false) equals `present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Some(false) is present")
expect(bool_payload(false)).to_equal("present")
```

</details>

#### nil bool is absent

- nil bool is absent
   - Expected: bool_payload(nil) equals `absent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nil bool is absent")
expect(bool_payload(nil)).to_equal("absent")
```

</details>

#### Some(0.0) is present

- Some(0.0) is present
   - Expected: float_payload(0.0) equals `present`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Some(0.0) is present")
expect(float_payload(0.0)).to_equal("present")
```

</details>

#### nil float is absent

- nil float is absent
   - Expected: float_payload(nil) equals `absent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nil float is absent")
expect(float_payload(nil)).to_equal("absent")
```

</details>

#### nil text is absent

- nil text is absent
   - Expected: text_payload(nil) equals `absent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nil text is absent")
expect(text_payload(nil)).to_equal("absent")
```

</details>

#### assert accepts Some(0) as present

- assert accepts Some(0) as present
   - Expected: assert_consumer(0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("assert accepts Some(0) as present")
expect(assert_consumer(0)).to_equal(true)
```

</details>

<details>
<summary>Advanced: loop body counts falsy-but-present options</summary>

#### loop body counts falsy-but-present options

- loop body counts falsy-but-present options
   - Expected: filter_consumer([0, nil, 5, nil]) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loop body counts falsy-but-present options")
expect(filter_consumer([0, nil, 5, nil])).to_equal(2)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/03_system/interpreter/exists_check_consumer_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ExistsCheck consumer class - falsy payloads across consumers.
- ExistsCheck consumer class - falsy payloads across consumers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `9b45919e50c1061eb069e14a140f7d87b373653596a2031f4c7885c25a272eec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b45919e50c1061eb069e14a140f7d87b373653596a2031f4c7885c25a272eec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b45919e50c1061eb069e14a140f7d87b373653596a2031f4c7885c25a272eec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/interpreter/exists_check_consumer_class_spec.spl
mirror: doc/06_spec/03_system/interpreter/exists_check_consumer_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/interpreter/exists_check_consumer_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/interpreter/exists_check_consumer_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/interpreter/exists_check_consumer_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/interpreter/exists_check_consumer_class_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'and consumer treats Some(0) as present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/interpreter/exists_check_consumer_class_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'and consumer treats nil as absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/interpreter/exists_check_consumer_class_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'or consumer treats Some(0) as present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
