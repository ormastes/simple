# Deprecated Items Removed Spec

> Canary spec for AC-5: verifies that the replacement APIs for all 13 real `@deprecated` items work correctly after Team G removes the deprecated methods.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Deprecated Items Removed Spec

Canary spec for AC-5: verifies that the replacement APIs for all 13 real `@deprecated` items work correctly after Team G removes the deprecated methods.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-allow-suppressions |
| Category | Testing |
| Difficulty | 1/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/quality/code_quality/deprecated_removed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Canary spec for AC-5: verifies that the replacement APIs for all 13 real
`@deprecated` items work correctly after Team G removes the deprecated methods.

NOTE: These specs verify the *replacement method works*. They cannot directly
assert that the deprecated method is gone — that is a grep gate at phase 7-verify:
  `rg -F '@deprecated' src/lib/nogc_sync_mut/ src/compiler_rust/lib/std/src/`
should return zero results after Team G completes.

These specs exercise Set.has / intersect / diff / sym_diff, Map.has,
String.upper / lower / each, List.each, and Path.ext.
They WILL PASS right now (replacement methods already exist). Their purpose
is to lock the replacement contract so it cannot regress.

## Scenarios

### AC-5 Set deprecated replacements

#### AC-5: Set.has returns true for a member element

- AC-5: Set.has returns true for a member element
   - Expected: s.has("Alice") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: Set.has returns true for a member element")
var s = Set.new()
s.insert("Alice")
expect(s.has("Alice")).to_equal(true)
```

</details>

#### AC-5: Set.has returns false for a missing element

- AC-5: Set.has returns false for a missing element
   - Expected: s.has("Bob") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: Set.has returns false for a missing element")
var s = Set.new()
s.insert("Alice")
expect(s.has("Bob")).to_equal(false)
```

</details>

#### AC-5: Set.intersect returns common elements only

- AC-5: Set.intersect returns common elements only
   - Expected: result.has("y") is true
   - Expected: result.has("x") is false
   - Expected: result.has("z") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: Set.intersect returns common elements only")
var a = Set.new()
a.insert("x")
a.insert("y")
var b = Set.new()
b.insert("y")
b.insert("z")
val result = set_intersection(a, b)
expect(result.has("y")).to_equal(true)
expect(result.has("x")).to_equal(false)
expect(result.has("z")).to_equal(false)
```

</details>

#### AC-5: Set.diff returns elements only in self

- AC-5: Set.diff returns elements only in self
   - Expected: result.has("x") is true
   - Expected: result.has("y") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: Set.diff returns elements only in self")
var a = Set.new()
a.insert("x")
a.insert("y")
var b = Set.new()
b.insert("y")
b.insert("z")
val result = set_difference(a, b)
expect(result.has("x")).to_equal(true)
expect(result.has("y")).to_equal(false)
```

</details>

#### AC-5: Set.sym_diff returns elements in exactly one set

- AC-5: Set.sym_diff returns elements in exactly one set
   - Expected: result.has("x") is true
   - Expected: result.has("z") is true
   - Expected: result.has("y") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: Set.sym_diff returns elements in exactly one set")
var a = Set.new()
a.insert("x")
a.insert("y")
var b = Set.new()
b.insert("y")
b.insert("z")
val result = set_symmetric_difference(a, b)
expect(result.has("x")).to_equal(true)
expect(result.has("z")).to_equal(true)
expect(result.has("y")).to_equal(false)
```

</details>

### AC-5 Map deprecated replacements

#### AC-5: Map.has returns true when key present

- AC-5: Map.has returns true when key present
   - Expected: m.has("name") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: Map.has returns true when key present")
var m = Map.new()
m.insert("name", "Alice")
expect(m.has("name")).to_equal(true)
```

</details>

#### AC-5: Map.has returns false when key absent

- AC-5: Map.has returns false when key absent
   - Expected: m.has("age") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: Map.has returns false when key absent")
var m = Map.new()
m.insert("name", "Alice")
expect(m.has("age")).to_equal(false)
```

</details>

### AC-5 String deprecated replacements

#### AC-5: String.upper converts to uppercase

- AC-5: String.upper converts to uppercase
   - Expected: s.upper() equals `HELLO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: String.upper converts to uppercase")
val s = "hello"
expect(s.upper()).to_equal("HELLO")
```

</details>

#### AC-5: String.lower converts to lowercase

- AC-5: String.lower converts to lowercase
   - Expected: s.lower() equals `world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: String.lower converts to lowercase")
val s = "WORLD"
expect(s.lower()).to_equal("world")
```

</details>

#### AC-5: String.each iterates over characters

- AC-5: String.each iterates over characters
   - Expected: seen.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: String.each iterates over characters")
val s = "abc"
var seen: [text] = []
each(s, \c:
    seen.push(c.to_string())
)
expect(seen.len()).to_equal(3)
```

</details>

### AC-5 List deprecated replacements

#### AC-5: List.each iterates over all elements

- AC-5: List.each iterates over all elements
   - Expected: sum equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: List.each iterates over all elements")
val items = [1, 2, 3]
var seen: [i64] = []
items.each(\n:
    seen.push(n)
)
var sum = 0
for n in seen:
    sum = sum + n
expect(sum).to_equal(6)
```

</details>

### AC-5 Path deprecated replacements

#### AC-5: Path.ext returns the file extension

- AC-5: Path.ext returns the file extension
   - Expected: extension("report.md") equals `md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: Path.ext returns the file extension")
expect(extension("report.md")).to_equal("md")
```

</details>

#### AC-5: Path.ext returns empty string for no extension

- AC-5: Path.ext returns empty string for no extension
   - Expected: extension("Makefile") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-5: Path.ext returns empty string for no extension")
expect(extension("Makefile")).to_equal("")
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `58bbe181ace2caa58ed944058ca48e29059b5396e9a764229189b52649a2e49f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58bbe181ace2caa58ed944058ca48e29059b5396e9a764229189b52649a2e49f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58bbe181ace2caa58ed944058ca48e29059b5396e9a764229189b52649a2e49f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/quality/code_quality/deprecated_removed_spec.spl
mirror: doc/06_spec/03_system/quality/code_quality/deprecated_removed_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/quality/code_quality/deprecated_removed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/code_quality/deprecated_removed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/code_quality/deprecated_removed_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/quality/code_quality/deprecated_removed_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: Set.has returns true for a member element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/deprecated_removed_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: Set.has returns false for a missing element' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/code_quality/deprecated_removed_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5: Set.intersect returns common elements only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
