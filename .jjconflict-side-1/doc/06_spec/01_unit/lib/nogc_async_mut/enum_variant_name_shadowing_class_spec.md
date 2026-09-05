# Enum Variant Name Shadowing Class Specification

> Tests covering enum variants are not shadowed by same-named globals.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum Variant Name Shadowing Class Specification

## Scenarios

### enum variants are not shadowed by same-named globals

#### control: a non-colliding variant round-trips through a struct field

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- control: a non-colliding variant round-trips through a struct field
   - Expected: wrap(Shadowed.Plain).tag == Shadowed.Plain is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("control: a non-colliding variant round-trips through a struct field")
expect(wrap(Shadowed.Plain).tag == Shadowed.Plain).to_equal(true)
```

</details>

#### FIRST variant position colliding with a struct

- FIRST variant position colliding with a struct
   - Expected: wrap(Shadowed.Alpha).tag == Shadowed.Alpha is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("FIRST variant position colliding with a struct")
expect(wrap(Shadowed.Alpha).tag == Shadowed.Alpha).to_equal(true)
```

</details>

#### MIDDLE variant position colliding with a struct

- MIDDLE variant position colliding with a struct
   - Expected: wrap(Shadowed.Middle).tag == Shadowed.Middle is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("MIDDLE variant position colliding with a struct")
expect(wrap(Shadowed.Middle).tag == Shadowed.Middle).to_equal(true)
```

</details>

#### LAST variant position colliding with a struct

- LAST variant position colliding with a struct
   - Expected: wrap(Shadowed.Omega).tag == Shadowed.Omega is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("LAST variant position colliding with a struct")
# Position matters to this spec because the filed instance happened to
# be the last variant, which is what made it look like a discriminant
# defect. If only this one failed, position -- not collision -- would be
# the axis.
expect(wrap(Shadowed.Omega).tag == Shadowed.Omega).to_equal(true)
```

</details>

#### a variant colliding with a FUNCTION, not a struct

- a variant colliding with a FUNCTION, not a struct
   - Expected: wrap(Shadowed.Solo).tag == Shadowed.Solo is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a variant colliding with a FUNCTION, not a struct")
# The bare-name fallback tries `functions` BEFORE `classes`, so a
# function collision is a distinct path to the same wrong answer.
expect(wrap(Shadowed.Solo).tag == Shadowed.Solo).to_equal(true)
```

</details>

#### a colliding variant literal is not equal to a different variant

- a colliding variant literal is not equal to a different variant
   - Expected: Shadowed.Alpha == Shadowed.Omega is false
   - Expected: wrap(Shadowed.Alpha).tag == Shadowed.Omega is false
   - Expected: wrap(Shadowed.Omega).tag == Shadowed.Alpha is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a colliding variant literal is not equal to a different variant")
# Guards the degenerate 'fix' where every comparison returns true.
expect(Shadowed.Alpha == Shadowed.Omega).to_equal(false)
expect(wrap(Shadowed.Alpha).tag == Shadowed.Omega).to_equal(false)
expect(wrap(Shadowed.Omega).tag == Shadowed.Alpha).to_equal(false)
```

</details>

#### the colliding global itself is still reachable and unchanged

- the colliding global itself is still reachable and unchanged
   - Expected: Alpha(n: 5).n equals `5`
   - Expected: Solo() equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("the colliding global itself is still reachable and unchanged")
# The fix must not steal the plain name: `Alpha` alone is still the
# struct, only `Shadowed.Alpha` is the variant.
expect(Alpha(n: 5).n).to_equal(5)
expect(Solo()).to_equal(-1)
```

</details>

#### == agrees with match for every colliding variant

- == agrees with match for every colliding variant
   - Expected: agreed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("== agrees with match for every colliding variant")
# These two routes disagreed under the defect: patterns resolved the
# variant correctly while `==` silently compared against a constructor.
# Any future regression that repairs only one route is caught here.
var agreed = true
val cases = [Shadowed.Alpha, Shadowed.Plain, Shadowed.Middle, Shadowed.Solo, Shadowed.Omega]
var i = 0
while i < cases.len():
    val held = wrap(cases[i]).tag
    var by_match = false
    match held:
        case Shadowed.Alpha:
            by_match = (cases[i] == Shadowed.Alpha)
        case Shadowed.Plain:
            by_match = (cases[i] == Shadowed.Plain)
        case Shadowed.Middle:
            by_match = (cases[i] == Shadowed.Middle)
        case Shadowed.Solo:
            by_match = (cases[i] == Shadowed.Solo)
        case Shadowed.Omega:
            by_match = (cases[i] == Shadowed.Omega)
    if not by_match:
        agreed = false
    i = i + 1
expect(agreed).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/enum_variant_name_shadowing_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering enum variants are not shadowed by same-named globals.
- enum variants are not shadowed by same-named globals

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9100a9c4eb9687ae3bc2d05b67ced8f88c4ca2ccf048cbeacbd4d965e8dd568b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9100a9c4eb9687ae3bc2d05b67ced8f88c4ca2ccf048cbeacbd4d965e8dd568b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9100a9c4eb9687ae3bc2d05b67ced8f88c4ca2ccf048cbeacbd4d965e8dd568b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_async_mut/enum_variant_name_shadowing_class_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/enum_variant_name_shadowing_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/enum_variant_name_shadowing_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/enum_variant_name_shadowing_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/enum_variant_name_shadowing_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/enum_variant_name_shadowing_class_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'control: a non-colliding variant round-trips through a struct field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/enum_variant_name_shadowing_class_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FIRST variant position colliding with a struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/enum_variant_name_shadowing_class_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MIDDLE variant position colliding with a struct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
