# Array `.at(i)` is a bounds-checked Option accessor, not an alias for `[i]`

> `.at(i)` returns `Some(element)` for an in-range index and `None` otherwise. It is *not* the same operation as `[i]`: `[i]` yields the element directly and has no way to report absence, while `.at(i)` is the safe accessor that ~161 call sites across the tree consume with `match`/`unwrap`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Array `.at(i)` is a bounds-checked Option accessor, not an alias for `[i]`

`.at(i)` returns `Some(element)` for an in-range index and `None` otherwise. It is *not* the same operation as `[i]`: `[i]` yields the element directly and has no way to report absence, while `.at(i)` is the safe accessor that ~161 call sites across the tree consume with `match`/`unwrap`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib / collection accessors |
| Status | Active |
| Source | `test/01_unit/lib/common/array_at_option_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`.at(i)` returns `Some(element)` for an in-range index and `None` otherwise. It
is *not* the same operation as `[i]`: `[i]` yields the element directly and has
no way to report absence, while `.at(i)` is the safe accessor that ~161 call
sites across the tree consume with `match`/`unwrap`.

Before the fix the Rust seed had no array `at` at all — only the *text* one
(`"char_at" | "at" => rt_string_char_at`). Every `arr.at(i)` therefore fell
through the unhandled-method path to `Value::Nil`, which reads as `None`. That
is the same value a genuinely out-of-range read produces, so every in-range hit
silently took the `None` branch with no error and no crash.

That failure shape is why the in-range assertions below matter more than the
out-of-range ones. `at(99) == None` passed even when `.at()` was completely
unimplemented; only `at(0) == Some(10)` can tell the two apart. Each in-range
assertion here is RED against the unpatched seed.

## Coverage

- in-range hit (first, interior, and the `len - 1` boundary)
- out-of-range: `len` exactly, and far past the end
- negative index — must be `None`, never a wrap-around to a huge positive index
- empty container
- index 3 specifically, and the *element value* 3, because the nil sentinel is 3
- `.at()` against `[i]` on the same array, so the two cannot silently diverge

## Syntax

```simple
match xs.at(0):
    Some(v): v
    None: -1
```

## Scenarios

### array .at() Option accessor

#### returns Some(element) for an in-range index

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### returns Some at the last valid index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xs: [i64] = [10, 20, 30, 40, 50]
assert_equal(at_or_absent(xs, 4), 50)
assert_true(is_present(xs, 4))
```

</details>

#### returns None at exactly len, the first invalid index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xs: [i64] = [10, 20, 30, 40, 50]
assert_equal(at_or_absent(xs, 5), SENTINEL_ABSENT)
assert_false(is_present(xs, 5))
```

</details>

#### returns None far past the end

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xs: [i64] = [10, 20, 30, 40, 50]
assert_equal(at_or_absent(xs, 99), SENTINEL_ABSENT)
```

</details>

#### returns None for a negative index rather than wrapping around

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xs: [i64] = [10, 20, 30, 40, 50]
assert_equal(at_or_absent(xs, -1), SENTINEL_ABSENT)
assert_equal(at_or_absent(xs, -100), SENTINEL_ABSENT)
```

</details>

#### returns None on an empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e: [i64] = []
assert_equal(at_or_absent(e, 0), SENTINEL_ABSENT)
assert_false(is_present(e, 0))
```

</details>

#### handles index 3, the nil sentinel value, as an ordinary index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xs: [i64] = [10, 20, 30, 40, 50]
assert_equal(at_or_absent(xs, 3), 40)
assert_true(is_present(xs, 3))
```

</details>

#### reports an element whose value is 3 as present, not absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xs: [i64] = [3, 3, 3]
assert_equal(at_or_absent(xs, 0), 3)
assert_equal(at_or_absent(xs, 2), 3)
assert_true(is_present(xs, 1))
assert_equal(at_or_absent(xs, 3), SENTINEL_ABSENT)
```

</details>

#### reports an element whose value is 0 as present, not absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xs: [i64] = [0, 0]
assert_equal(at_or_absent(xs, 0), 0)
assert_true(is_present(xs, 0))
```

</details>

#### agrees with [i] on every in-range index

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xs: [i64] = [7, 0, 3, 42, -5]
var i = 0
while i < xs.len():
    assert_equal(at_or_absent(xs, i), xs[i])
    i = i + 1
```

</details>

#### stays None for every index of a single-element array except 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val xs: [i64] = [99]
assert_equal(at_or_absent(xs, 0), 99)
assert_equal(at_or_absent(xs, 1), SENTINEL_ABSENT)
assert_equal(at_or_absent(xs, -1), SENTINEL_ABSENT)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `88e556b06284785bf0b7fbe34e96b46260d12eeb59b5eb2ac71918614f804d27`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88e556b06284785bf0b7fbe34e96b46260d12eeb59b5eb2ac71918614f804d27`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88e556b06284785bf0b7fbe34e96b46260d12eeb59b5eb2ac71918614f804d27`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/common/array_at_option_spec.spl
mirror: doc/06_spec/01_unit/lib/common/array_at_option_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/array_at_option_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/array_at_option_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/array_at_option_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/common/array_at_option_spec.spl:73:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns Some(element) for an in-range index' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/array_at_option_spec.spl:81:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns Some at the last valid index' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/array_at_option_spec.spl:86:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns None at exactly len, the first invalid index' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/array_at_option_spec.spl:91:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns None far past the end' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
