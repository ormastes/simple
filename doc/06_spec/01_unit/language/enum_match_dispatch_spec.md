# Enum Match Dispatch Specification

> Tests covering match on enum -- unit variants, match on enum -- payload variants, match on enum -- wildcard arm does not steal a matching case.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum Match Dispatch Specification

## Scenarios

### match on enum -- unit variants

#### dispatches Kind.A to the A arm

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- dispatches Kind.A to the A arm
   - Expected: describe_kind(Kind.A) equals `kind-A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches Kind.A to the A arm")
expect(describe_kind(Kind.A)).to_equal("kind-A")
```

</details>

#### dispatches Kind.B to the B arm

- dispatches Kind.B to the B arm
   - Expected: describe_kind(Kind.B) equals `kind-B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches Kind.B to the B arm")
expect(describe_kind(Kind.B)).to_equal("kind-B")
```

</details>

#### dispatches Kind.C to the C arm

- dispatches Kind.C to the C arm
   - Expected: describe_kind(Kind.C) equals `kind-C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches Kind.C to the C arm")
expect(describe_kind(Kind.C)).to_equal("kind-C")
```

</details>

### match on enum -- payload variants

#### dispatches Circle(r) and binds the payload

- dispatches Circle(r) and binds the payload
   - Expected: describe_shape(Shape.Circle(2.5)) equals `circle:2.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches Circle(r) and binds the payload")
expect(describe_shape(Shape.Circle(2.5))).to_equal("circle:2.5")
```

</details>

#### dispatches Rect(w, h) and binds both payload fields

- dispatches Rect(w, h) and binds both payload fields
   - Expected: describe_shape(Shape.Rect(3.0, 4.0)) equals `rect:3.0x4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches Rect(w, h) and binds both payload fields")
expect(describe_shape(Shape.Rect(3.0, 4.0))).to_equal("rect:3.0x4.0")
```

</details>

#### dispatches the unit-variant Point arm among payload siblings

- dispatches the unit-variant Point arm among payload siblings
   - Expected: describe_shape(Shape.Point) equals `point`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches the unit-variant Point arm among payload siblings")
expect(describe_shape(Shape.Point)).to_equal("point")
```

</details>

### match on enum -- wildcard arm does not steal a matching case

#### does not fall through Kind.C to the wildcard

- does not fall through Kind.C to the wildcard
   - Expected: hit_wildcard is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not fall through Kind.C to the wildcard")
var hit_wildcard = false
match Kind.C:
    case Kind.A: hit_wildcard = false
    case Kind.B: hit_wildcard = false
    case Kind.C: hit_wildcard = false
    case _: hit_wildcard = true
expect(hit_wildcard).to_equal(false)
```

</details>

#### takes the wildcard only when no prior arm matches (out-of-band value via helper)

- takes the wildcard only when no prior arm matches (out-of-band value via helper)
   - Expected: seen equals `wildcard`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("takes the wildcard only when no prior arm matches (out-of-band value via helper)")
var seen = "unset"
match Shape.Point:
    case Shape.Circle(_): seen = "circle"
    case Shape.Rect(_, _): seen = "rect"
    case _: seen = "wildcard"
# Point has its own arm above Shape's match in describe_shape, but this
# inline match omits it deliberately to prove the wildcard still
# catches an unmatched payload-enum variant rather than silently
# falling through (doc/08_tracking/bug/match_enum_fallthrough_silent_2026-08-01.md).
expect(seen).to_equal("wildcard")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/language/enum_match_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering match on enum -- unit variants, match on enum -- payload variants, match on enum -- wildcard arm does not steal a matching case.
- match on enum -- unit variants
- match on enum -- payload variants
- match on enum -- wildcard arm does not steal a matching case

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `0e7bef7cd3ec6769f30ed5d5fa05e3de8daf00bfb545b053a1d0fac65d05c1aa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e7bef7cd3ec6769f30ed5d5fa05e3de8daf00bfb545b053a1d0fac65d05c1aa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e7bef7cd3ec6769f30ed5d5fa05e3de8daf00bfb545b053a1d0fac65d05c1aa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/language/enum_match_dispatch_spec.spl
mirror: doc/06_spec/01_unit/language/enum_match_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/enum_match_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/enum_match_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/enum_match_dispatch_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches Kind.A to the A arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/enum_match_dispatch_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches Kind.B to the B arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/language/enum_match_dispatch_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches Kind.C to the C arm' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
