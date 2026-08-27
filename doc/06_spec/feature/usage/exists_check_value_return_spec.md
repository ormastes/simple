# Existence Check Value Return (.? → T?) Specification

> After the `.?` return-type change, the operator returns `T?` instead of `bool`. This enables pattern binding (`if val x = expr.?:`) and nil coalescing (`expr.? ?? default`).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Existence Check Value Return (.? → T?) Specification

After the `.?` return-type change, the operator returns `T?` instead of `bool`. This enables pattern binding (`if val x = expr.?:`) and nil coalescing (`expr.? ?? default`).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2100-VALUE-RETURN |
| Category | Syntax |
| Difficulty | 3/5 |
| Status | Implemented (requires compiler rebuild) |
| Research | doc/01_research/text_validity_presence_pattern_2026-02-24.md |
| Source | `test/feature/usage/exists_check_value_return_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

After the `.?` return-type change, the operator returns `T?` instead of `bool`.
This enables pattern binding (`if val x = expr.?:`) and nil coalescing
(`expr.? ?? default`).

## Behavior

`.?` returns `T?` — value if present, nil if absent. Option types pass through
without double-wrapping. See `doc/06_spec/app/compiler/feature/exists_check_spec.md` for the
full type/return table.

## Related

- `exists_check_spec.spl` — boolean truthiness tests
- `elif_val_pattern_binding_spec.spl` — `if val` / `elif val` patterns

## Scenarios

### Existence Check Value Return (.? -> T?)

#### nil coalescing with text

#### returns value for non-empty string via ??

- returns value for non-empty string via ??


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns value for non-empty string via ??")
val s = "hello"
val result = s.? ?? "default"
expect result == "hello"
```

</details>

#### returns default for empty string via ??

- returns default for empty string via ??


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns default for empty string via ??")
val s = ""
val result = s.? ?? "default"
expect result == "default"
```

</details>

#### chains multiple ?? fallbacks

- chains multiple ?? fallbacks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("chains multiple ?? fallbacks")
val a = ""
val b = ""
val c = "found"
val result = a.? ?? b.? ?? c.? ?? "none"
expect result == "found"
```

</details>

#### nil coalescing with collections

#### returns list for non-empty list via ??

- returns list for non-empty list via ??


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns list for non-empty list via ??")
val items = [1, 2, 3]
val result = items.? ?? [0]
expect result == [1, 2, 3]
```

</details>

#### returns default for empty list via ??

- returns default for empty list via ??


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns default for empty list via ??")
val empty: List<i32> = []
val result = empty.? ?? [0]
expect result == [0]
```

</details>

#### pattern binding with if val

#### binds non-empty string

- binds non-empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binds non-empty string")
val input = "hello"
var result = "unset"
if val name = input.?:
    result = name
expect result == "hello"
```

</details>

#### skips binding for empty string

- skips binding for empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("skips binding for empty string")
val input = ""
var result = "default"
if val name = input.?:
    result = name
expect result == "default"
```

</details>

#### binds non-empty list

- binds non-empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binds non-empty list")
val items = [10, 20]
var result = "unset"
if val bound = items.?:
    result = "bound"
expect result == "bound"
```

</details>

#### skips binding for empty list

- skips binding for empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("skips binding for empty list")
val empty: List<i32> = []
var result = "default"
if val bound = empty.?:
    result = "bound"
expect result == "default"
```

</details>

#### Option pass-through

#### passes through Some value

- passes through Some value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes through Some value")
val opt: Option<i32> = Some(42)
val result = opt.? ?? 0
expect result == 42
```

</details>

#### returns default for None

- returns default for None


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns default for None")
val opt: Option<i32> = None
val result = opt.? ?? 0
expect result == 0
```

</details>

#### binds Some value with if val

- binds Some value with if val


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("binds Some value with if val")
val opt: Option<text> = Some("hi")
var result = "unset"
if val s = opt.?:
    result = s
expect result == "hi"
```

</details>

#### primitive values

#### returns number via ??

- returns number via ??


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns number via ??")
val n = 42
val result = n.? ?? 0
expect result == 42
```

</details>

#### returns zero via ??

- returns zero via ??


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns zero via ??")
val n = 0
val result = n.? ?? -1
expect result == 0
```

</details>

#### chained with methods

#### works with trim and ??

- works with trim and ??


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with trim and ??")
val s = "  hello  "
val result = s.trim.? ?? "empty"
expect result == "hello"
```

</details>

#### returns default for empty trim result

- returns default for empty trim result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns default for empty trim result")
val s = ""
val result = s.trim.? ?? "empty"
expect result == "empty"
```

</details>

#### works with list.first and ??

- works with list.first and ??


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with list.first and ??")
val items = [42, 99]
val result = items.first.? ?? 0
expect result == 42
```

</details>

#### returns default for empty list.first

- returns default for empty list.first


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns default for empty list.first")
val empty: List<i32> = []
val result = empty.first.? ?? 0
expect result == 0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** `doc/01_research/text_validity_presence_pattern_2026-02-24.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `61e6bcd4c3b3deca0db7a977c5614326d4338bbfc45e691158b627120b275ac1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61e6bcd4c3b3deca0db7a977c5614326d4338bbfc45e691158b627120b275ac1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61e6bcd4c3b3deca0db7a977c5614326d4338bbfc45e691158b627120b275ac1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/exists_check_value_return_spec.spl
mirror: doc/06_spec/feature/usage/exists_check_value_return_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/exists_check_value_return_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/exists_check_value_return_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/exists_check_value_return_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns value for non-empty string via ??' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/exists_check_value_return_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns default for empty string via ??' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/exists_check_value_return_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chains multiple ?? fallbacks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
