# Generic class / generic impl lower as NON-EMITTABLE templates (#158 Phase C)

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic class / generic impl lower as NON-EMITTABLE templates (#158 Phase C)

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mono/generic_class_impl_template_lowering_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/mono/generic_class_impl_template_lowering_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### generic class and generic impl lower as non-emittable templates

#### raises no declaration-site monomorphization gate error

- Lower a module declaring impl Poll2<T> and class Fut<T>
- Confirm the #158 declaration gates no longer fire
   - Expected: gate_error_count(out.errors) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Lower a module declaring impl Poll2<T> and class Fut<T>")
val out = lower_one("phase_c_tpl", SRC)
step("Confirm the #158 declaration gates no longer fire")
expect(gate_error_count(out.errors)).to_equal(0)
```

</details>

#### lowers the module without errors at all

- Lower the same module
- Confirm the uninstantiated templates are not an error
   - Expected: out.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Lower the same module")
val out = lower_one("phase_c_tpl2", SRC)
step("Confirm the uninstantiated templates are not an error")
expect(out.errors.len()).to_equal(0)
```

</details>

#### records the generic class as a template

- Lower and inspect HirClass.is_generic_template
   - Expected: flagged is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Lower and inspect HirClass.is_generic_template")
val out = lower_one("phase_c_tpl3", SRC)
var flagged = false
for cn in out.module.classes.keys():
    val c = out.module.classes[cn]
    if c.name == "Fut":
        flagged = c.is_generic_template
expect(flagged).to_equal(true)
```

</details>

#### flags at least one method as a non-emittable template

- Lower and count is_generic_template functions
- Both the impl method and the class method are templates
   - Expected: template_function_count(out.module) > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Lower and count is_generic_template functions")
val out = lower_one("phase_c_tpl4", SRC)
step("Both the impl method and the class method are templates")
expect(template_function_count(out.module) > 0).to_equal(true)
```

</details>

#### keeps the non-generic entry function emittable

- main() must NOT be flagged as a template
   - Expected: main_is_template is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("main() must NOT be flagged as a template")
val out = lower_one("phase_c_tpl5", SRC)
var main_is_template = true
for sym in out.module.functions.keys():
    val f: HirFunction = out.module.functions[sym]
    if f.name == "main":
        main_is_template = f.is_generic_template
expect(main_is_template).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `04e5b7fc0cd9ec44a501f48867ec62e1fa0aabae193536f85cc6c274dff8a031`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `04e5b7fc0cd9ec44a501f48867ec62e1fa0aabae193536f85cc6c274dff8a031`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `04e5b7fc0cd9ec44a501f48867ec62e1fa0aabae193536f85cc6c274dff8a031`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/mono/generic_class_impl_template_lowering_spec.spl
mirror: doc/06_spec/01_unit/compiler/mono/generic_class_impl_template_lowering_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mono/generic_class_impl_template_lowering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mono/generic_class_impl_template_lowering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mono/generic_class_impl_template_lowering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mono/generic_class_impl_template_lowering_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'raises no declaration-site monomorphization gate error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mono/generic_class_impl_template_lowering_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers the module without errors at all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mono/generic_class_impl_template_lowering_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records the generic class as a template' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/compiler/mono/generic_class_impl_template_lowering_spec.spl. -->
