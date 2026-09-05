# text_advanced_levenshtein_spec

> Purpose: Prove that levenshtein_distance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# text_advanced_levenshtein_spec

Purpose: Prove that levenshtein_distance.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/text_advanced_levenshtein_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that levenshtein_distance.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### levenshtein_distance

#### reports the classic kitten/sitting distance of three

- reports the classic kitten/sitting distance of three
- Verify: reports the classic kitten/sitting distance of three
   - Expected: levenshtein_distance("kitten", "sitting") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports the classic kitten/sitting distance of three")
step("Verify: reports the classic kitten/sitting distance of three")
# @req: REQ-LIB-COMMON-001
# k->s, e->i, +g : three single-character edits.
expect(levenshtein_distance("kitten", "sitting")).to_equal(3)
```

</details>

#### counts a full replacement of every character

- counts a full replacement of every character
- Verify: counts a full replacement of every character
   - Expected: levenshtein_distance("abc", "xyz") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counts a full replacement of every character")
step("Verify: counts a full replacement of every character")
expect(levenshtein_distance("abc", "xyz")).to_equal(3)
```

</details>

#### counts pure insertions against the empty string

- counts pure insertions against the empty string
- Verify: counts pure insertions against the empty string
   - Expected: levenshtein_distance("", "abcd") equals `4`
   - Expected: levenshtein_distance("abcd", "") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counts pure insertions against the empty string")
step("Verify: counts pure insertions against the empty string")
expect(levenshtein_distance("", "abcd")).to_equal(4)
expect(levenshtein_distance("abcd", "")).to_equal(4)
```

</details>

#### counts a single substitution

- counts a single substitution
- Verify: counts a single substitution
   - Expected: levenshtein_distance("flaw", "flow") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counts a single substitution")
step("Verify: counts a single substitution")
expect(levenshtein_distance("flaw", "flow")).to_equal(1)
```

</details>

#### counts a single deletion

- counts a single deletion
- Verify: counts a single deletion
   - Expected: levenshtein_distance("cart", "car") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counts a single deletion")
step("Verify: counts a single deletion")
expect(levenshtein_distance("cart", "car")).to_equal(1)
```

</details>

#### still reports zero for identical strings

- still reports zero for identical strings
- Verify: still reports zero for identical strings
   - Expected: levenshtein_distance("same", "same") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still reports zero for identical strings")
step("Verify: still reports zero for identical strings")
expect(levenshtein_distance("same", "same")).to_equal(0)
```

</details>

#### is symmetric

- is symmetric
- Verify: is symmetric
   - Expected: levenshtein_distance("sunday", "saturday") equals `3`
   - Expected: levenshtein_distance("saturday", "sunday") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is symmetric")
step("Verify: is symmetric")
expect(levenshtein_distance("sunday", "saturday")).to_equal(3)
expect(levenshtein_distance("saturday", "sunday")).to_equal(3)
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

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5aeec968cebf7e1007e6d179617e5d762bde9a7d3d4091dcbc2bc728a0d2bb3f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5aeec968cebf7e1007e6d179617e5d762bde9a7d3d4091dcbc2bc728a0d2bb3f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5aeec968cebf7e1007e6d179617e5d762bde9a7d3d4091dcbc2bc728a0d2bb3f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/text_advanced_levenshtein_spec.spl
mirror: doc/06_spec/01_unit/lib/common/text_advanced_levenshtein_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/text_advanced_levenshtein_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/text_advanced_levenshtein_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/text_advanced_levenshtein_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/text_advanced_levenshtein_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the classic kitten/sitting distance of three' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_advanced_levenshtein_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts a full replacement of every character' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_advanced_levenshtein_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counts pure insertions against the empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
