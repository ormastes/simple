# Option Wrapped Enum Match Variant Specification

> Tests covering match_enum_variant_pattern unwraps an Option wrapper before comparing a non-Option variant tag.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option Wrapped Enum Match Variant Specification

## Scenarios

### match_enum_variant_pattern unwraps an Option wrapper before comparing a non-Option variant tag

#### matches a plain boxed user-enum value against its own variant (baseline, unaffected by the fix)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches a plain boxed user-enum value against its own variant (baseline, unaffected by the fix)
   - Expected: match_enum_variant_pattern(e_val, "A", []) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches a plain boxed user-enum value against its own variant (baseline, unaffected by the fix)")
val e_val = make_boxed_enum("E::A", "A", val_make_int(7))
expect(match_enum_variant_pattern(e_val, "A", [])).to_equal(true)
```

</details>

#### does NOT match a plain boxed user-enum value against a different variant

- does NOT match a plain boxed user-enum value against a different variant
   - Expected: match_enum_variant_pattern(e_val, "C", []) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT match a plain boxed user-enum value against a different variant")
val e_val = make_boxed_enum("E::A", "A", val_make_int(7))
expect(match_enum_variant_pattern(e_val, "C", [])).to_equal(false)
```

</details>

#### matches an Option::Some-wrapped payload-carrying variant against the inner variant name (the bug)

- matches an Option::Some-wrapped payload-carrying variant against the inner variant name (the bug)
   - Expected: match_enum_variant_pattern(wrapped, "A", []) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches an Option::Some-wrapped payload-carrying variant against the inner variant name (the bug)")
val inner = make_boxed_enum("E::A", "A", val_make_int(7))
val wrapped = make_boxed_enum("Option::Some", "Some", inner)
expect(match_enum_variant_pattern(wrapped, "A", [])).to_equal(true)
```

</details>

#### matches an Option::Some-wrapped payloadless variant against the inner variant name

- matches an Option::Some-wrapped payloadless variant against the inner variant name
   - Expected: match_enum_variant_pattern(wrapped, "C", []) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches an Option::Some-wrapped payloadless variant against the inner variant name")
val inner = make_boxed_enum("E::C", "C", val_make_int(0))
val wrapped = make_boxed_enum("Option::Some", "Some", inner)
expect(match_enum_variant_pattern(wrapped, "C", [])).to_equal(true)
```

</details>

#### does NOT match an Option::Some wrapper against an unrelated inner variant name

- does NOT match an Option::Some wrapper against an unrelated inner variant name
   - Expected: match_enum_variant_pattern(wrapped, "C", []) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT match an Option::Some wrapper against an unrelated inner variant name")
val inner = make_boxed_enum("E::A", "A", val_make_int(7))
val wrapped = make_boxed_enum("Option::Some", "Some", inner)
expect(match_enum_variant_pattern(wrapped, "C", [])).to_equal(false)
```

</details>

#### does NOT match an Option::None wrapper against any real variant name

- does NOT match an Option::None wrapper against any real variant name
   - Expected: match_enum_variant_pattern(wrapped, "A", []) is false
   - Expected: match_enum_variant_pattern(wrapped, "C", []) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT match an Option::None wrapper against any real variant name")
val wrapped = make_boxed_enum("Option::None", "None", val_make_int(0))
expect(match_enum_variant_pattern(wrapped, "A", [])).to_equal(false)
expect(match_enum_variant_pattern(wrapped, "C", [])).to_equal(false)
```

</details>

#### still matches the wrapper itself (not the inner enum) when the pattern's own variant IS Some/None

- still matches the wrapper itself (not the inner enum) when the pattern's own variant IS Some/None
   - Expected: match_enum_variant_pattern(wrapped, "Some", []) is true
   - Expected: match_enum_variant_pattern(wrapped, "None", []) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still matches the wrapper itself (not the inner enum) when the pattern's own variant IS Some/None")
val inner = make_boxed_enum("E::A", "A", val_make_int(7))
val wrapped = make_boxed_enum("Option::Some", "Some", inner)
expect(match_enum_variant_pattern(wrapped, "Some", [])).to_equal(true)
expect(match_enum_variant_pattern(wrapped, "None", [])).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/interpreter/option_wrapped_enum_match_variant_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering match_enum_variant_pattern unwraps an Option wrapper before comparing a non-Option variant tag.
- match_enum_variant_pattern unwraps an Option wrapper before comparing a non-Option variant tag

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `11e2311c841ff93785982e6291d57d70406f513533d8364ad32578c670b9e685`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `11e2311c841ff93785982e6291d57d70406f513533d8364ad32578c670b9e685`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `11e2311c841ff93785982e6291d57d70406f513533d8364ad32578c670b9e685`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler_core/interpreter/option_wrapped_enum_match_variant_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/interpreter/option_wrapped_enum_match_variant_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/interpreter/option_wrapped_enum_match_variant_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/interpreter/option_wrapped_enum_match_variant_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/interpreter/option_wrapped_enum_match_variant_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches a plain boxed user-enum value against its own variant (baseline, unaffected by the fix)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/interpreter/option_wrapped_enum_match_variant_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does NOT match a plain boxed user-enum value against a different variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/interpreter/option_wrapped_enum_match_variant_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches an Option::Some-wrapped payload-carrying variant against the inner variant name (the bug)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
