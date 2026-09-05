# nil_presence_idioms_spec

> As a Simple developer testing whether an optional value is present,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nil_presence_idioms_spec

As a Simple developer testing whether an optional value is present,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/nil_presence_idioms_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a Simple developer testing whether an optional value is present,
    I want `== nil` / `!= nil` and `if val x = opt.?:` to mean presence,
    so that a legitimately-zero or legitimately-empty payload is not
    mistaken for an absent one.

## Scenarios

### nil-presence idioms (engine-agnostic)

#### Option<i64> holding Some(0) is NOT nil

- Option<i64> holding Some(0) is NOT nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("Option<i64> holding Some(0) is NOT nil")
val v = some_i(0)
expect_not(v == nil)
assert_true(v != nil)
```

</details>

#### Option<i64> holding Some(5) is NOT nil

- Option<i64> holding Some(5) is NOT nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("Option<i64> holding Some(5) is NOT nil")
val v = some_i(5)
expect_not(v == nil)
assert_true(v != nil)
```

</details>

#### Option<i64> holding None IS nil

- Option<i64> holding None IS nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("Option<i64> holding None IS nil")
val v = none_i()
assert_true(v == nil)
expect_not(v != nil)
```

</details>

#### Option<text> holding an empty string is NOT nil

- Option<text> holding an empty string is NOT nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("Option<text> holding an empty string is NOT nil")
val v = some_t("")
expect_not(v == nil)
assert_true(v != nil)
```

</details>

#### Option<text> holding None IS nil

- Option<text> holding None IS nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("Option<text> holding None IS nil")
val v = none_t()
assert_true(v == nil)
expect_not(v != nil)
```

</details>

#### == nil and != nil are always mutual opposites

- == nil and != nil are always mutual opposites
   - Expected: a == nil equals `not (a != nil)`
   - Expected: b == nil equals `not (b != nil)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("== nil and != nil are always mutual opposites")
val a = some_i(0)
val b = none_i()
expect(a == nil).to_equal(not (a != nil))
expect(b == nil).to_equal(not (b != nil))
```

</details>

#### if val binds a Some(0) payload and yields 0

- if val binds a Some(0) payload and yields 0
   - Expected: got equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("if val binds a Some(0) payload and yields 0")
val v = some_i(0)
var bound = false
var got = 0 - 999
if val x = v.?:
    bound = true
    got = x
assert_true(bound)
expect(got).to_equal(0)
```

</details>

#### if val binds a Some(5) payload

- if val binds a Some(5) payload
   - Expected: got equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("if val binds a Some(5) payload")
val v = some_i(5)
var bound = false
var got = 0 - 999
if val x = v.?:
    bound = true
    got = x
assert_true(bound)
expect(got).to_equal(5)
```

</details>

#### if val does not bind a None payload

- if val does not bind a None payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("if val does not bind a None payload")
val v = none_i()
var bound = false
if val x = v.?:
    bound = true
expect_not(bound)
```

</details>

### search-index sentinel idioms

#### index_of returns 0 for a match at the start, not a nil-ish value

- index_of returns 0 for a match at the start, not a nil-ish value
   - Expected: s.index_of("a") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("index_of returns 0 for a match at the start, not a nil-ish value")
val s = "abc"
expect(s.index_of("a")).to_equal(0)
```

</details>

#### index_of returns -1 when the needle is absent

- index_of returns -1 when the needle is absent
   - Expected: s.index_of("z") equals `0 - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("index_of returns -1 when the needle is absent")
val s = "abc"
expect(s.index_of("z")).to_equal(0 - 1)
```

</details>

#### last_index_of returns -1 when the needle is absent

- last_index_of returns -1 when the needle is absent
   - Expected: s.last_index_of("z") equals `0 - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("last_index_of returns -1 when the needle is absent")
val s = "abc"
expect(s.last_index_of("z")).to_equal(0 - 1)
```

</details>

#### find returns 0 for a match at index 0

- find returns 0 for a match at index 0
   - Expected: s.find("$") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("find returns 0 for a match at index 0")
val s = "$abc"
expect(s.find("$")).to_equal(0)
```

</details>

#### find returns -1 when the needle is absent

- find returns -1 when the needle is absent
   - Expected: s.find("z") equals `0 - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("find returns -1 when the needle is absent")
val s = "$abc"
expect(s.find("z")).to_equal(0 - 1)
```

</details>

#### the `< 0` guard accepts a match at index 0 and rejects not-found

- the `< 0` guard accepts a match at index 0 and rejects not-found


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LANGUAGE
step("the `< 0` guard accepts a match at index 0 and rejects not-found")
val s = "$abc"
val hit = s.find("$")
val miss = s.find("z")
expect_not(hit < 0)
assert_true(miss < 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LANGUAGE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2ca9223e6da3aa0896964e6d37e286895c9f46b1a1a28b2f1a3fabaaf6221195`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2ca9223e6da3aa0896964e6d37e286895c9f46b1a1a28b2f1a3fabaaf6221195`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2ca9223e6da3aa0896964e6d37e286895c9f46b1a1a28b2f1a3fabaaf6221195`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/language/nil_presence_idioms_spec.spl
mirror: doc/06_spec/01_unit/language/nil_presence_idioms_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/nil_presence_idioms_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/nil_presence_idioms_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/nil_presence_idioms_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/language/nil_presence_idioms_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Option<i64> holding Some(0) is NOT nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/nil_presence_idioms_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Option<i64> holding Some(5) is NOT nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/nil_presence_idioms_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Option<i64> holding None IS nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
