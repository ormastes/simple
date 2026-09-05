# Text Method Erased Receiver Parity Specification

> Tests covering text predicate owner precedence, text.trim, text.to_lower, text.split, text.replace, text.rfind.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Method Erased Receiver Parity Specification

## Scenarios

### text predicate owner precedence

#### keeps text starts_with ahead of a same-named custom struct method

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps text starts_with ahead of a same-named custom struct method


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps text starts_with ahead of a same-named custom struct method")
val opener: text = "@media (min-width: 1px)"
check(opener.starts_with("@"))
```

</details>

#### retains custom starts_with dispatch for a ByteSpan receiver

- retains custom starts_with dispatch for a ByteSpan receiver


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retains custom starts_with dispatch for a ByteSpan receiver")
val bytes: [u8] = [64u8, 109u8, 101u8, 100u8, 105u8, 97u8]
val prefix: [u8] = [64u8]
check(ByteSpan.new(bytes).starts_with(ByteSpan.new(prefix)))
```

</details>

### text.trim

#### removes leading and trailing whitespace

- removes leading and trailing whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes leading and trailing whitespace")
check("  hi  ".trim() == "hi")
```

</details>

#### returns the original text unchanged when there is no whitespace to trim

- returns the original text unchanged when there is no whitespace to trim


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the original text unchanged when there is no whitespace to trim")
check("hi".trim() == "hi")
```

</details>

#### returns an empty string when trimming an empty string

- returns an empty string when trimming an empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty string when trimming an empty string")
check("".trim() == "")
```

</details>

#### collapses an all-whitespace string to empty

- collapses an all-whitespace string to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collapses an all-whitespace string to empty")
check("   ".trim() == "")
```

</details>

### text.to_lower

#### lowercases an all-uppercase ASCII string

- lowercases an all-uppercase ASCII string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lowercases an all-uppercase ASCII string")
check("HELLO WORLD".to_lower() == "hello world")
```

</details>

#### leaves an already-lowercase string unchanged

- leaves an already-lowercase string unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves an already-lowercase string unchanged")
check("hello world".to_lower() == "hello world")
```

</details>

#### leaves an empty string unchanged

- leaves an empty string unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves an empty string unchanged")
check("".to_lower() == "")
```

</details>

#### case-folds accented unicode letters

- case-folds accented unicode letters


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("case-folds accented unicode letters")
check("HÉLLO WÖRLD".to_lower() == "héllo wörld")
```

</details>

#### leaves already-lowercase unicode content unchanged

- leaves already-lowercase unicode content unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves already-lowercase unicode content unchanged")
check("héllo wörld".to_lower() == "héllo wörld")
```

</details>

### text.split

#### splits on every occurrence of a single-character delimiter

- splits on every occurrence of a single-character delimiter


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits on every occurrence of a single-character delimiter")
val parts = "a,b,c".split(",")
check(parts.len() == 3)
check(parts[0] == "a")
check(parts[1] == "b")
check(parts[2] == "c")
```

</details>

#### preserves empty fields for consecutive delimiters

- preserves empty fields for consecutive delimiters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves empty fields for consecutive delimiters")
val parts = "a,b,,c".split(",")
check(parts.len() == 4)
check(parts[2] == "")
```

</details>

#### produces a leading and trailing empty field when the delimiter sits at both ends

- produces a leading and trailing empty field when the delimiter sits at both ends


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces a leading and trailing empty field when the delimiter sits at both ends")
val parts = ",a,b,".split(",")
check(parts.len() == 4)
check(parts[0] == "")
check(parts[3] == "")
```

</details>

#### returns a single-element list for a string with no delimiter occurrence

- returns a single-element list for a string with no delimiter occurrence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a single-element list for a string with no delimiter occurrence")
val parts = "abc".split(",")
check(parts.len() == 1)
check(parts[0] == "abc")
```

</details>

#### returns a single empty-string element when splitting an empty string

- returns a single empty-string element when splitting an empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a single empty-string element when splitting an empty string")
val parts = "".split(",")
check(parts.len() == 1)
check(parts[0] == "")
```

</details>

#### splits on a multibyte unicode delimiter without corrupting surrounding bytes

- splits on a multibyte unicode delimiter without corrupting surrounding bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits on a multibyte unicode delimiter without corrupting surrounding bytes")
val parts = "héllo".split("é")
check(parts.len() == 2)
check(parts[0] == "h")
check(parts[1] == "llo")
```

</details>

### text.replace

#### replaces every occurrence of a multi-match needle

- replaces every occurrence of a multi-match needle


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces every occurrence of a multi-match needle")
check("aXbXc".replace("X", "-") == "a-b-c")
```

</details>

#### returns the original text unchanged when the needle never matches

- returns the original text unchanged when the needle never matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the original text unchanged when the needle never matches")
check("abc".replace("z", "-") == "abc")
```

</details>

#### handles a replacement that expands the string

- handles a replacement that expands the string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles a replacement that expands the string")
check("aaa".replace("a", "bb") == "bbbbbb")
```

</details>

#### leaves an empty string unchanged

- leaves an empty string unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves an empty string unchanged")
check("".replace("a", "b") == "")
```

</details>

#### replaces a multibyte unicode needle correctly

- replaces a multibyte unicode needle correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces a multibyte unicode needle correctly")
val out = "héllo wörld".replace("ö", "o")
check(out == "héllo world")
```

</details>

### text.rfind

#### returns the index of the last occurrence for a multi-match needle

- returns the index of the last occurrence for a multi-match needle


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the index of the last occurrence for a multi-match needle")
check("abcabc".rfind("bc") == 4)
```

</details>

#### returns -1 when the needle never occurs

- returns -1 when the needle never occurs


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 when the needle never occurs")
check("abcabc".rfind("zz") == -1)
```

</details>

#### returns 0 when the only match is at the very start

- returns 0 when the only match is at the very start


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 when the only match is at the very start")
check("abc".rfind("a") == 0)
```

</details>

#### returns -1 when searching an empty haystack for a non-empty needle

- returns -1 when searching an empty haystack for a non-empty needle


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns -1 when searching an empty haystack for a non-empty needle")
check("".rfind("x") == -1)
```

</details>

#### locates a multibyte unicode needle by byte offset in a repeated pattern

- locates a multibyte unicode needle by byte offset in a repeated pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("locates a multibyte unicode needle by byte offset in a repeated pattern")
check("héllo héllo".rfind("héllo") == 7)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/text_method_erased_receiver_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering text predicate owner precedence, text.trim, text.to_lower, text.split, text.replace, text.rfind.
- text predicate owner precedence
- text.trim
- text.to_lower
- text.split
- text.replace
- text.rfind

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
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

- Canonical SPipe generation for source `db6ab060445597f102a03e4baa2545b7da50f2af8921740a041a186e3733e354`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db6ab060445597f102a03e4baa2545b7da50f2af8921740a041a186e3733e354`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db6ab060445597f102a03e4baa2545b7da50f2af8921740a041a186e3733e354`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir/text_method_erased_receiver_parity_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/text_method_erased_receiver_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/text_method_erased_receiver_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/text_method_erased_receiver_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/text_method_erased_receiver_parity_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps text starts_with ahead of a same-named custom struct method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/text_method_erased_receiver_parity_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains custom starts_with dispatch for a ByteSpan receiver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/text_method_erased_receiver_parity_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes leading and trailing whitespace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
