# Exact Specification

> Tests covering exact single-pattern: absolute positions, exact: edge cases, exact: cross-check vs naive oracle, exact: Two-Way periodic memory path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Exact Specification

## Scenarios

### exact single-pattern: absolute positions

#### memmem finds 'ana' in 'banana' at index 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### two_way finds 'ana' in 'banana' at index 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = two_way(hay_of("banana"), pat_of("ana"))
expect(r.start()).to_equal(1)
```

</details>

#### boyer_moore_horspool finds 'ana' in 'banana' at index 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = boyer_moore_horspool(hay_of("banana"), pat_of("ana"))
expect(r.start()).to_equal(1)
```

</details>

#### find_all reports overlapping 'ana' in 'banana' at 1 and 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all = find_all(hay_of("banana"), pat_of("ana"))
val starts = starts_of(all)
expect(lists_equal(starts, [1, 3])).to_equal(true)
```

</details>

#### absent pattern returns no-match sentinel (-1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = memmem(hay_of("banana"), pat_of("xyz"))
expect(r.start()).to_equal(0 - 1)
```

</details>

#### absent pattern find_all returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all = find_all(hay_of("banana"), pat_of("xyz"))
expect(all.len()).to_equal(0)
```

</details>

#### pattern at start matches index 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = two_way(hay_of("hello world"), pat_of("hello"))
expect(r.start()).to_equal(0)
```

</details>

#### pattern at end matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "world" starts at index 6 of "hello world"
val r = boyer_moore_horspool(hay_of("hello world"), pat_of("world"))
expect(r.start()).to_equal(6)
```

</details>

#### match span has correct length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = memmem(hay_of("banana"), pat_of("ana"))
expect(r.length()).to_equal(3)
```

</details>

#### match span end index is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = memmem(hay_of("banana"), pat_of("ana"))
expect(r.end()).to_equal(4)
```

</details>

### exact: edge cases

#### pattern longer than haystack -> no match (memmem)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = memmem(hay_of("hi"), pat_of("hello"))
expect(r.start()).to_equal(0 - 1)
```

</details>

#### pattern longer than haystack -> no match (two_way)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = two_way(hay_of("hi"), pat_of("hello"))
expect(r.start()).to_equal(0 - 1)
```

</details>

#### pattern longer than haystack -> no match (BMH)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = boyer_moore_horspool(hay_of("hi"), pat_of("hello"))
expect(r.start()).to_equal(0 - 1)
```

</details>

#### empty pattern matches at index 0 (memmem)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = memmem(hay_of("abc"), pat_of(""))
expect(r.start()).to_equal(0)
```

</details>

#### empty pattern find_all matches every position 0..=len

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all = find_all(hay_of("abc"), pat_of(""))
# "abc" has len 3 -> positions 0,1,2,3
expect(all.len()).to_equal(4)
```

</details>

#### empty haystack with non-empty pattern -> no match

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = two_way(hay_of(""), pat_of("a"))
expect(r.start()).to_equal(0 - 1)
```

</details>

#### single-char pattern found at all positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val all = find_all(hay_of("aXaXa"), pat_of("a"))
val starts = starts_of(all)
expect(lists_equal(starts, [0, 2, 4])).to_equal(true)
```

</details>

### exact: cross-check vs naive oracle

#### agrees on 'ana' in 'banana'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_agrees("banana", "ana")).to_equal(true)
```

</details>

#### agrees on overlap fixture 'aaa' in 'aaaaa'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_agrees("aaaaa", "aaa")).to_equal(true)
```

</details>

#### agrees on periodic 'abab' in 'ababab'

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_agrees("ababab", "abab")).to_equal(true)
```

</details>

#### agrees on pattern-at-start

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_agrees("hello world", "hello")).to_equal(true)
```

</details>

#### agrees on pattern-at-end

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_agrees("hello world", "world")).to_equal(true)
```

</details>

#### agrees on absent pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_agrees("abcdef", "gh")).to_equal(true)
```

</details>

#### agrees on pattern longer than haystack

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_agrees("ab", "abcdef")).to_equal(true)
```

</details>

#### agrees on repeated-suffix pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_agrees("xabcabcabz", "abcab")).to_equal(true)
```

</details>

#### agrees on single byte pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_agrees("mississippi", "s")).to_equal(true)
```

</details>

#### find_all all-positions match naive_all for 'iss' in 'mississippi'

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val starts = starts_of(find_all(hay_of("mississippi"), pat_of("iss")))
val oracle = naive_all(bytes_of("mississippi"), bytes_of("iss"))
expect(lists_equal(starts, oracle)).to_equal(true)
```

</details>

#### find_all all-positions match naive_all for periodic 'aa' in 'aaaa'

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val starts = starts_of(find_all(hay_of("aaaa"), pat_of("aa")))
val oracle = naive_all(bytes_of("aaaa"), bytes_of("aa"))
expect(lists_equal(starts, oracle)).to_equal(true)
```

</details>

### exact: Two-Way periodic memory path

#### two_way agrees with oracle on long periodic 'abcabc' in repeated text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_agrees("abcabcabcabcabc", "abcabc")).to_equal(true)
```

</details>

#### two_way agrees on all-same long pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_agrees("aaaaaaaaaa", "aaaaaa")).to_equal(true)
```

</details>

#### two_way agrees when periodic pattern is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_agrees("abcabcabd", "abcabcabc")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/exact_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering exact single-pattern: absolute positions, exact: edge cases, exact: cross-check vs naive oracle, exact: Two-Way periodic memory path.
- exact single-pattern: absolute positions
- exact: edge cases
- exact: cross-check vs naive oracle
- exact: Two-Way periodic memory path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
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

- Canonical SPipe generation for source `14e8b2e5306909912544e3a328cb13b03630cba37df67d4dd8ed57e8c84d3967`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `14e8b2e5306909912544e3a328cb13b03630cba37df67d4dd8ed57e8c84d3967`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `14e8b2e5306909912544e3a328cb13b03630cba37df67d4dd8ed57e8c84d3967`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/lib/common/search/exact_spec.spl
mirror: doc/06_spec/01_unit/lib/common/search/exact_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/search/exact_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/search/exact_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/search/exact_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/common/search/exact_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/search/exact_spec.spl:113:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'memmem finds 'ana' in 'banana' at index 1' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/search/exact_spec.spl:119:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'two_way finds 'ana' in 'banana' at index 1' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/search/exact_spec.spl:123:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'boyer_moore_horspool finds 'ana' in 'banana' at index 1' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/search/exact_spec.spl:127:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'find_all reports overlapping 'ana' in 'banana' at 1 and 3' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
