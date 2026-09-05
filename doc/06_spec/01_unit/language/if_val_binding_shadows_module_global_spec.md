# `if val` bindings are locals and shadow module globals

> An `if val NAME = expr:` binding is a LOCAL of the enclosing frame. Reading

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `if val` bindings are locals and shadow module globals

An `if val NAME = expr:` binding is a LOCAL of the enclosing frame. Reading

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language |
| Status | Stable |
| Source | `test/01_unit/language/if_val_binding_shadows_module_global_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

An `if val NAME = expr:` binding is a LOCAL of the enclosing frame. Reading
NAME inside the bound body must yield the bound payload, even when a
module-level global of the same name exists.

## Scope and Preconditions

The module global here is deliberately FUNCTION-valued. The seed's identifier
read (`interpreter/expr/literals.rs`) prefers `MODULE_GLOBALS` over any binding
the frame does not mark local, and `Env::insert` — which every `if val` site
used — does not mark one. The bound name therefore read back as the global,
and a function-valued global makes that visible as a value rather than as a
plausible-looking wrong number.

## Primary Workflow

`probe(7)` binds `get_value` to `7` and returns it. Pre-fix it returned
`<fn:helper>`, which downstream became
`undefined field 'id': cannot access field on value of type 'function'` far
from here — see
doc/08_tracking/bug/single_module_native_build_dies_in_any_escape_and_mir_for_2026-08-22.md

## Evidence and Provenance

Measured on the deployed seed: pre-fix `p=<fn:helper>`, post-fix `p=7`.

## Scenarios

### if val bindings shadow a same-named module global

#### returns the bound payload, not the function-valued global

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### takes the else path when the optional is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(probe(nil)).to_equal(-1)
```

</details>

#### shadows for a text payload too

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(probe_text("bound")).to_equal("bound")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `2c498211b4dd6df4988ae49c106adc7514e30f034d4869220d39468c2d8b7f74`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2c498211b4dd6df4988ae49c106adc7514e30f034d4869220d39468c2d8b7f74`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2c498211b4dd6df4988ae49c106adc7514e30f034d4869220d39468c2d8b7f74`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/language/if_val_binding_shadows_module_global_spec.spl
mirror: doc/06_spec/01_unit/language/if_val_binding_shadows_module_global_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=70 oracle=90
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/language/if_val_binding_shadows_module_global_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/language/if_val_binding_shadows_module_global_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/language/if_val_binding_shadows_module_global_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/language/if_val_binding_shadows_module_global_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/language/if_val_binding_shadows_module_global_spec.spl:60:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'returns the bound payload, not the function-valued global' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/language/if_val_binding_shadows_module_global_spec.spl:66:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'takes the else path when the optional is empty' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/language/if_val_binding_shadows_module_global_spec.spl:70:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'shadows for a text payload too' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
