# Class Method Bodies Reachable Specification

> Tests covering class-embedded method bodies reachable from HirModule.functions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Class Method Bodies Reachable Specification

## Scenarios

### class-embedded method bodies reachable from HirModule.functions

#### makes both HirFunctions of a 2-method class present in module.functions with non-empty bodies

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- makes both HirFunctions of a 2-method class present in module.functions with non-empty bodies
   - Expected: hir_lowering.errors.len() equals `0`
   - Expected: found_class is true
   - Expected: fn_.body.stmts.len() > 0 is true
   - Expected: has_assign is true
   - Expected: fn_.body.stmts.len() > 0 is true
   - Expected: has_assign is true
   - Expected: found_set_value is true
   - Expected: found_double is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("makes both HirFunctions of a 2-method class present in module.functions with non-empty bodies")
val src = "class Box:\n" +
    "    value: i64\n" +
    "    me set_value(next: i64) -> i64:\n" +
    "        self.value = next\n" +
    "        self.value\n" +
    "    me double(next: i64) -> i64:\n" +
    "        self.value = next * 2\n" +
    "        self.value\n"
val parsed = parse_full_frontend(src, "testdata/clsm_two_methods.spl", "clsm_two_methods", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("testdata/clsm_two_methods.spl")
val hir = hir_lowering.lower_module(parsed)
expect(hir_lowering.errors.len()).to_equal(0)

var found_class = false
for class_ in hir.classes.values():
    if class_.name == "Box":
        found_class = true
expect(found_class).to_equal(true)

var found_set_value = false
var found_double = false
for fn_ in hir.functions.values():
    if fn_.name == "set_value":
        found_set_value = true
        expect(fn_.body.stmts.len() > 0).to_equal(true)
        # Walk for a known statement: the first statement of the
        # method body is the `self.value = ...` assignment.
        var has_assign = false
        match fn_.body.stmts[0].kind:
            case Assign(_, _, _):
                has_assign = true
            case _:
                pass
        expect(has_assign).to_equal(true)
    if fn_.name == "double":
        found_double = true
        expect(fn_.body.stmts.len() > 0).to_equal(true)
        var has_assign = false
        match fn_.body.stmts[0].kind:
            case Assign(_, _, _):
                has_assign = true
            case _:
                pass
        expect(has_assign).to_equal(true)
expect(found_set_value).to_equal(true)
expect(found_double).to_equal(true)
```

</details>

#### keeps both a class method and a top-level fn reachable in the same module

- keeps both a class method and a top-level fn reachable in the same module
   - Expected: fn_.body.stmts.len() >= 0 is true
   - Expected: fn_.body.stmts.len() > 0 is true
   - Expected: found_helper is true
   - Expected: found_method is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps both a class method and a top-level fn reachable in the same module")
val src = "fn helper() -> i64:\n" +
    "    99\n" +
    "\n" +
    "class Box:\n" +
    "    value: i64\n" +
    "    me set_value(next: i64) -> i64:\n" +
    "        self.value = next\n" +
    "        self.value\n"
val parsed = parse_full_frontend(src, "testdata/clsm_mixed.spl", "clsm_mixed", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("testdata/clsm_mixed.spl")
val hir = hir_lowering.lower_module(parsed)

var found_helper = false
var found_method = false
for fn_ in hir.functions.values():
    if fn_.name == "helper":
        found_helper = true
        expect(fn_.body.stmts.len() >= 0).to_equal(true)
    if fn_.name == "set_value":
        found_method = true
        expect(fn_.body.stmts.len() > 0).to_equal(true)
expect(found_helper).to_equal(true)
expect(found_method).to_equal(true)
```

</details>

#### keeps an impl-block method reachable too (regression, pre-existing merge path)

- keeps an impl-block method reachable too (regression, pre-existing merge path)
   - Expected: hir_lowering.errors.len() equals `0`
   - Expected: fn_.body.stmts.len() > 0 is true
   - Expected: found_bump is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps an impl-block method reachable too (regression, pre-existing merge path)")
val src = "struct Counter:\n" +
    "    n: i64\n" +
    "\n" +
    "impl Counter:\n" +
    "    me bump():\n" +
    "        self.n = self.n + 1\n"
val parsed = parse_full_frontend(src, "testdata/clsm_impl_regression.spl", "clsm_impl_regression", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("testdata/clsm_impl_regression.spl")
val hir = hir_lowering.lower_module(parsed)
expect(hir_lowering.errors.len()).to_equal(0)

var found_bump = false
for fn_ in hir.functions.values():
    if fn_.name == "bump":
        found_bump = true
        expect(fn_.body.stmts.len() > 0).to_equal(true)
expect(found_bump).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/class_method_bodies_reachable_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering class-embedded method bodies reachable from HirModule.functions.
- class-embedded method bodies reachable from HirModule.functions

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5abd36bad3a46c486b8e8ed518563ba25095ef6d41f0f5d0d75fe973a8f1de92`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5abd36bad3a46c486b8e8ed518563ba25095ef6d41f0f5d0d75fe973a8f1de92`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5abd36bad3a46c486b8e8ed518563ba25095ef6d41f0f5d0d75fe973a8f1de92`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/hir/class_method_bodies_reachable_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/class_method_bodies_reachable_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/class_method_bodies_reachable_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/class_method_bodies_reachable_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/class_method_bodies_reachable_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/class_method_bodies_reachable_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'makes both HirFunctions of a 2-method class present in module.functions with non-empty bodies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/class_method_bodies_reachable_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps both a class method and a top-level fn reachable in the same module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/class_method_bodies_reachable_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps an impl-block method reachable too (regression, pre-existing merge path)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
