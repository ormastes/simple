# Two-arg text.index_of(needle, start) Specification

> Purpose: Prove that text.index_of(needle, start) core.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Two-arg text.index_of(needle, start) Specification

Purpose: Prove that text.index_of(needle, start) core.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-INDEXOF-START-001 |
| Category | Runtime |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/bugs/text_index_of_start_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that text.index_of(needle, start) core.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### text.index_of(needle, start) core

#### found at or after start

#### finds the first occurrence from 0

- finds the first occurrence from 0
- Verify: finds the first occurrence from 0
   - Expected: s.index_of("needle", 0) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("finds the first occurrence from 0")
step("Verify: finds the first occurrence from 0")
# @req: REQ-BUGS-001
val s = "prefix-needle-needle"
expect(s.index_of("needle", 0)).to_equal(7)
```

</details>

#### skips an occurrence before start and reports the later one

- skips an occurrence before start and reports the later one
- Verify: skips an occurrence before start and reports the later one
   - Expected: s.index_of("needle", 8) equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("skips an occurrence before start and reports the later one")
step("Verify: skips an occurrence before start and reports the later one")
val s = "prefix-needle-needle"
expect(s.index_of("needle", 8)).to_equal(14)
```

</details>

#### finds a needle located at exactly start

- finds a needle located at exactly start
- Verify: finds a needle located at exactly start
   - Expected: s.index_of("needle", 7) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("finds a needle located at exactly start")
step("Verify: finds a needle located at exactly start")
val s = "prefix-needle-needle"
expect(s.index_of("needle", 7)).to_equal(7)
```

</details>

#### finds the second occurrence when start is just past the first

- finds the second occurrence when start is just past the first
- Verify: finds the second occurrence when start is just past the first
   - Expected: s.index_of("abc", 1) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("finds the second occurrence when start is just past the first")
step("Verify: finds the second occurrence when start is just past the first")
val s = "abcabc"
expect(s.index_of("abc", 1)).to_equal(3)
```

</details>

#### not found

#### returns -1 when the needle is absent

- returns -1 when the needle is absent
- Verify: returns -1 when the needle is absent
   - Expected: s.index_of("zzz", 0) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("returns -1 when the needle is absent")
step("Verify: returns -1 when the needle is absent")
val s = "prefix-needle-needle"
expect(s.index_of("zzz", 0)).to_equal(-1)
```

</details>

#### returns -1 when the only occurrence is before start

- returns -1 when the only occurrence is before start
- Verify: returns -1 when the only occurrence is before start
   - Expected: s.index_of("abc", 1) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("returns -1 when the only occurrence is before start")
step("Verify: returns -1 when the only occurrence is before start")
val s = "abcdef"
expect(s.index_of("abc", 1)).to_equal(-1)
```

</details>

#### start clamping

#### clamps a negative start to 0

- clamps a negative start to 0
- Verify: clamps a negative start to 0
   - Expected: s.index_of("needle", -5) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("clamps a negative start to 0")
step("Verify: clamps a negative start to 0")
val s = "prefix-needle-needle"
expect(s.index_of("needle", -5)).to_equal(7)
```

</details>

#### returns -1 when start is past the end

- returns -1 when start is past the end
- Verify: returns -1 when start is past the end
   - Expected: s.index_of("needle", 99) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("returns -1 when start is past the end")
step("Verify: returns -1 when start is past the end")
val s = "prefix-needle-needle"
expect(s.index_of("needle", 99)).to_equal(-1)
```

</details>

#### returns -1 when start equals the length

- returns -1 when start equals the length
- Verify: returns -1 when start equals the length
   - Expected: s.index_of("a", 3) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("returns -1 when start equals the length")
step("Verify: returns -1 when start equals the length")
val s = "abc"
expect(s.index_of("a", 3)).to_equal(-1)
```

</details>

#### empty needle

#### returns start for an empty needle inside the string

- returns start for an empty needle inside the string
- Verify: returns start for an empty needle inside the string
   - Expected: s.index_of("", 5) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("returns start for an empty needle inside the string")
step("Verify: returns start for an empty needle inside the string")
val s = "abcdef"
expect(s.index_of("", 5)).to_equal(5)
```

</details>

#### returns the length for an empty needle past the end

- returns the length for an empty needle past the end
- Verify: returns the length for an empty needle past the end
   - Expected: s.index_of("", 99) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("returns the length for an empty needle past the end")
step("Verify: returns the length for an empty needle past the end")
val s = "abc"
expect(s.index_of("", 99)).to_equal(3)
```

</details>

### text.index_of(needle, start) byte offsets on multi-byte text

#### 2-byte sequences (é is 2 bytes)

#### reports byte offsets, not character offsets

- reports byte offsets, not character offsets
- Verify: reports byte offsets, not character offsets
   - Expected: s.len() equals `12`
   - Expected: s.index_of("Z", 0) equals `5`
   - Expected: s.index_of("Z", 6) equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("reports byte offsets, not character offsets")
step("Verify: reports byte offsets, not character offsets")
# "caféZcaféZ": c0 a1 f2 é3,4 Z5 c6 a7 f8 é9,10 Z11 — len 12.
val s = "caféZcaféZ"
expect(s.len()).to_equal(12)  # oracle: 12 — named expected value from the requirement
expect(s.index_of("Z", 0)).to_equal(5)
# From byte 6 the next Z is at byte 11 (character index would
# be 9 — asserting 11 pins BYTE semantics).
expect(s.index_of("Z", 6)).to_equal(11)
```

</details>

#### agrees with one-arg index_of at start 0

- agrees with one-arg index_of at start 0
- Verify: agrees with one-arg index_of at start 0
   - Expected: s.index_of("Z", 0) equals `s.index_of("Z")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("agrees with one-arg index_of at start 0")
step("Verify: agrees with one-arg index_of at start 0")
val s = "caféZcaféZ"
expect(s.index_of("Z", 0)).to_equal(s.index_of("Z"))
```

</details>

#### 3-byte sequences (CJK)

#### finds an ASCII needle after CJK text by byte offset

- finds an ASCII needle after CJK text by byte offset
- Verify: finds an ASCII needle after CJK text by byte offset
   - Expected: s.len() equals `20`
   - Expected: s.index_of("a", 0) equals `9`
   - Expected: s.index_of("a", 10) equals `19`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("finds an ASCII needle after CJK text by byte offset")
step("Verify: finds an ASCII needle after CJK text by byte offset")
# "日本語a日本語a": each CJK char is 3 bytes — a at 9 and 19.
val s = "日本語a日本語a"
expect(s.len()).to_equal(20)  # oracle: 20 — named expected value from the requirement
expect(s.index_of("a", 0)).to_equal(9)
expect(s.index_of("a", 10)).to_equal(19)
```

</details>

#### 4-byte sequences (emoji)

#### finds a needle after an emoji by byte offset

- finds a needle after an emoji by byte offset
- Verify: finds a needle after an emoji by byte offset
   - Expected: s.len() equals `10`
   - Expected: s.index_of("x", 1) equals `5`
   - Expected: s.index_of("😀", 5) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("finds a needle after an emoji by byte offset")
step("Verify: finds a needle after an emoji by byte offset")
# "x😀x😀": x0 😀1-4 x5 😀6-9 — len 10.
val s = "x😀x😀"
expect(s.len()).to_equal(10)  # oracle: 10 — named expected value from the requirement
expect(s.index_of("x", 1)).to_equal(5)
expect(s.index_of("😀", 5)).to_equal(6)
```

</details>

#### start landing mid-codepoint

#### still finds a later needle when start splits a codepoint

- still finds a later needle when start splits a codepoint
- Verify: still finds a later needle when start splits a codepoint
   - Expected: s.index_of("Z", 4) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("still finds a later needle when start splits a codepoint")
step("Verify: still finds a later needle when start splits a codepoint")
# start 4 lands inside é (bytes 3,4); the scan is a byte scan,
# so the Z at byte 5 is still found.
val s = "caféZdef"
expect(s.index_of("Z", 4)).to_equal(5)
```

</details>

#### one-arg index_of stays byte-indexed in chained position

#### reports the byte index, not the character index, on a chained receiver

- reports the byte index, not the character index, on a chained receiver
- Verify: reports the byte index, not the character index, on a chained receiver
   - Expected: "  caféZdef  ".trim().index_of("Z") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("reports the byte index, not the character index, on a chained receiver")
step("Verify: reports the byte index, not the character index, on a chained receiver")
# The seed interpreter's chained-call fast path used to return
# s[..idx].chars().count() — a CHARACTER index (4 here) —
# silently diverging from every other index_of path. Byte index
# of Z in "caféZdef" is 5.
expect("  caféZdef  ".trim().index_of("Z")).to_equal(5)
```

</details>

#### agrees with the un-chained one-arg form

- agrees with the un-chained one-arg form
- Verify: agrees with the un-chained one-arg form
   - Expected: "  caféZdef  ".trim().index_of("Z") equals `s.index_of("Z")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("agrees with the un-chained one-arg form")
step("Verify: agrees with the un-chained one-arg form")
val s = "caféZdef"
expect("  caféZdef  ".trim().index_of("Z")).to_equal(s.index_of("Z"))
```

</details>

### text.index_of(needle, start) no longer leaks the error sentinel

#### sentinel pin

#### returns the real match, not 27, at start 0

- returns the real match, not 27, at start 0
- Verify: returns the real match, not 27, at start 0
   - Expected: r equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("returns the real match, not 27, at start 0")
step("Verify: returns the real match, not 27, at start 0")
# Before the fix EVERY two-arg call returned the tagged
# SPECIAL_ERROR sentinel 27 (while exiting 0). Expected value 7
# both differs from 27 and from the -1 miss value.
val s = "prefix-needle-needle"
val r = s.index_of("needle", 0)
expect(r).to_equal(7)  # oracle: 7 — named expected value from the requirement
expect_not(r == 27)
```

</details>

#### returns -1, not 27, for a genuine miss

- returns -1, not 27, for a genuine miss
- Verify: returns -1, not 27, for a genuine miss
   - Expected: r equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("returns -1, not 27, for a genuine miss")
step("Verify: returns -1, not 27, for a genuine miss")
val s = "short"
val r = s.index_of("absent", 0)
expect(r).to_equal(-1)  # oracle: -1 — named expected value from the requirement
expect_not(r == 27)
```

</details>

#### vacuity probe

#### executes assertions in this file (guard against empty bodies)

- executes assertions in this file (guard against empty bodies)
- Verify: executes assertions in this file (guard against empty bodies)
   - Expected: s.index_of("c", 1) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BUGS
step("executes assertions in this file (guard against empty bodies)")
step("Verify: executes assertions in this file (guard against empty bodies)")
# If spec discovery ever produced an empty body for this file,
# this deliberately non-trivial equality would not run; pairing
# a computed value with a constant keeps it un-foldable.
val s = "vacuity"
expect(s.index_of("c", 1)).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BUGS`
- `REQ-BUGS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `87c8a94d637c722b23fc43d6cd0a9aa9f582aad3dfffd6b729541545d2a5f2bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `87c8a94d637c722b23fc43d6cd0a9aa9f582aad3dfffd6b729541545d2a5f2bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `87c8a94d637c722b23fc43d6cd0a9aa9f582aad3dfffd6b729541545d2a5f2bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/bugs/text_index_of_start_spec.spl
mirror: doc/06_spec/01_unit/bugs/text_index_of_start_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/bugs/text_index_of_start_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/bugs/text_index_of_start_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/bugs/text_index_of_start_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/bugs/text_index_of_start_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds the first occurrence from 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/text_index_of_start_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips an occurrence before start and reports the later one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/bugs/text_index_of_start_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds a needle located at exactly start' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
