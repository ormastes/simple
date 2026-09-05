# array_index_of_spec

> Purpose: Prove that array index_of.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# array_index_of_spec

Purpose: Prove that array index_of.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/array_index_of_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that array index_of.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### array index_of

#### finds an i64 element at the first position

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finds an i64 element at the first position
- Verify: finds an i64 element at the first position
   - Expected: a.index_of(10) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("finds an i64 element at the first position")
step("Verify: finds an i64 element at the first position")
# @req: REQ-LANGUAGE-001
val a: [i64] = [10, 20, 30, 40, 50]
expect(a.index_of(10)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### finds an i64 element in the middle

- finds an i64 element in the middle
- Verify: finds an i64 element in the middle
   - Expected: a.index_of(30) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("finds an i64 element in the middle")
step("Verify: finds an i64 element in the middle")
val a: [i64] = [10, 20, 30, 40, 50]
expect(a.index_of(30)).to_equal(2)  # oracle: 2 — named expected value from the requirement
```

</details>

#### finds an i64 element at the last position

- finds an i64 element at the last position
- Verify: finds an i64 element at the last position
   - Expected: a.index_of(50) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("finds an i64 element at the last position")
step("Verify: finds an i64 element at the last position")
val a: [i64] = [10, 20, 30, 40, 50]
expect(a.index_of(50)).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

#### returns -1 for an absent i64 element

- returns -1 for an absent i64 element
- Verify: returns -1 for an absent i64 element
   - Expected: a.index_of(99) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("returns -1 for an absent i64 element")
step("Verify: returns -1 for an absent i64 element")
val a: [i64] = [10, 20, 30, 40, 50]
expect(a.index_of(99)).to_equal(-1)  # oracle: -1 — named expected value from the requirement
```

</details>

#### returns -1 on an empty i64 array

- returns -1 on an empty i64 array
- Verify: returns -1 on an empty i64 array
   - Expected: e.index_of(1) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("returns -1 on an empty i64 array")
step("Verify: returns -1 on an empty i64 array")
val e: [i64] = []
expect(e.index_of(1)).to_equal(-1)  # oracle: -1 — named expected value from the requirement
```

</details>

#### finds a text element at the first position

- finds a text element at the first position
- Verify: finds a text element at the first position
   - Expected: t.index_of("alpha") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("finds a text element at the first position")
step("Verify: finds a text element at the first position")
val t: [text] = ["alpha", "beta", "gamma"]
expect(t.index_of("alpha")).to_equal(0)
```

</details>

#### finds a text element at the last position

- finds a text element at the last position
- Verify: finds a text element at the last position
   - Expected: t.index_of("gamma") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("finds a text element at the last position")
step("Verify: finds a text element at the last position")
val t: [text] = ["alpha", "beta", "gamma"]
expect(t.index_of("gamma")).to_equal(2)
```

</details>

#### compares text elements by value, not by identity

- compares text elements by value, not by identity
- Verify: compares text elements by value, not by identity
   - Expected: t.index_of(needle) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("compares text elements by value, not by identity")
step("Verify: compares text elements by value, not by identity")
val t: [text] = ["alpha", "beta", "gamma"]
val needle = "be" + "ta"
expect(t.index_of(needle)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### returns -1 for an absent text element

- returns -1 for an absent text element
- Verify: returns -1 for an absent text element
   - Expected: t.index_of("zzz") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("returns -1 for an absent text element")
step("Verify: returns -1 for an absent text element")
val t: [text] = ["alpha", "beta", "gamma"]
expect(t.index_of("zzz")).to_equal(-1)
```

</details>

#### returns -1 on an empty text array

- returns -1 on an empty text array
- Verify: returns -1 on an empty text array
   - Expected: e.index_of("alpha") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("returns -1 on an empty text array")
step("Verify: returns -1 on an empty text array")
val e: [text] = []
expect(e.index_of("alpha")).to_equal(-1)
```

</details>

#### reports the FIRST occurrence when an element repeats

- reports the FIRST occurrence when an element repeats
- Verify: reports the FIRST occurrence when an element repeats
   - Expected: d.index_of(7) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("reports the FIRST occurrence when an element repeats")
step("Verify: reports the FIRST occurrence when an element repeats")
val d: [i64] = [7, 8, 7, 9]
expect(d.index_of(7)).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### agrees with contains on presence

- agrees with contains on presence
- Verify: agrees with contains on presence
   - Expected: a.index_of(20) >= 0 equals `a.contains(20)`
   - Expected: a.index_of(99) >= 0 equals `a.contains(99)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("agrees with contains on presence")
step("Verify: agrees with contains on presence")
val a: [i64] = [10, 20, 30]
expect(a.index_of(20) >= 0).to_equal(a.contains(20))
expect(a.index_of(99) >= 0).to_equal(a.contains(99))
```

</details>

#### does not regress text.index_of, which keeps its own -1 contract

- does not regress text.index_of, which keeps its own -1 contract
- Verify: does not regress text.index_of, which keeps its own -1 contract
   - Expected: s.index_of("h") equals `0`
   - Expected: s.index_of("llo") equals `2`
   - Expected: s.index_of("zzz") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("does not regress text.index_of, which keeps its own -1 contract")
step("Verify: does not regress text.index_of, which keeps its own -1 contract")
val s = "hello"
expect(s.index_of("h")).to_equal(0)
expect(s.index_of("llo")).to_equal(2)
expect(s.index_of("zzz")).to_equal(-1)
```

</details>

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

- `REQ-SSPEC-LANGUAGE`
- `REQ-LANGUAGE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cf0fe8b67a71382e6a6bba1c79d412144d1a53aca77d05b726d88bf36cecc122`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cf0fe8b67a71382e6a6bba1c79d412144d1a53aca77d05b726d88bf36cecc122`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cf0fe8b67a71382e6a6bba1c79d412144d1a53aca77d05b726d88bf36cecc122`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/language/array_index_of_spec.spl
mirror: doc/06_spec/01_unit/language/array_index_of_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/array_index_of_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/array_index_of_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/array_index_of_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/language/array_index_of_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds an i64 element at the first position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/array_index_of_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds an i64 element in the middle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/array_index_of_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds an i64 element at the last position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
