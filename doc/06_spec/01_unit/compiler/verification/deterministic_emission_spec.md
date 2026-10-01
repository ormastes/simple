# Deterministic Lean Emission Specification

> Verifies that LeanCodegen produces byte-identical output regardless of the order in which items (structures, inductives, functions, theorems, imports) are added. Both `emit()` and `generate()` must sort by `.name` before rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Deterministic Lean Emission Specification

Verifies that LeanCodegen produces byte-identical output regardless of the order in which items (structures, inductives, functions, theorems, imports) are added. Both `emit()` and `generate()` must sort by `.name` before rendering.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LEAN-DET-001 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/compiler/verification/deterministic_emission_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that LeanCodegen produces byte-identical output regardless of the
order in which items (structures, inductives, functions, theorems, imports)
are added. Both `emit()` and `generate()` must sort by `.name` before
rendering.

## Behavior

- All structured items are sorted alphabetically by name before emission
- Imports are sorted alphabetically before emission
- Two codegen instances with items added in different orders produce identical output

## Scenarios

### Deterministic Lean Emission

#### emit() determinism

#### produces identical output regardless of insertion order

- produces identical output regardless of insertion order
   - Expected: output_a equals `output_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 71 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces identical output regardless of insertion order")
# Build codegen A: add items in alphabetical order
var opts_a = codegen.LeanCodegenOptions.new()
opts_a = opts_a.with_module_name("DetTest")
var cg_a = codegen.LeanCodegen.new(opts_a)

var struct_alpha = codegen.LeanStructure.new("Alpha")
struct_alpha = struct_alpha.add_field("x", "Int")
var struct_beta = codegen.LeanStructure.new("Beta")
struct_beta = struct_beta.add_field("y", "Int")

cg_a = cg_a.add_structure(struct_alpha)
cg_a = cg_a.add_structure(struct_beta)

var func_add = codegen.LeanFunction.new("add")
func_add = func_add.add_param("a", "Nat")
func_add = func_add.with_return_type("Nat")
func_add = func_add.with_body("a")
var func_mul = codegen.LeanFunction.new("mul")
func_mul = func_mul.add_param("b", "Nat")
func_mul = func_mul.with_return_type("Nat")
func_mul = func_mul.with_body("b")

cg_a = cg_a.add_function(func_add)
cg_a = cg_a.add_function(func_mul)

var thm_a = codegen.LeanTheorem.new("add_comm", "a + b = b + a")
var thm_b = codegen.LeanTheorem.new("mul_comm", "a * b = b * a")
cg_a = cg_a.add_theorem(thm_a)
cg_a = cg_a.add_theorem(thm_b)

val output_a = cg_a.emit()

# Build codegen B: add items in REVERSE order
var opts_b = codegen.LeanCodegenOptions.new()
opts_b = opts_b.with_module_name("DetTest")
var cg_b = codegen.LeanCodegen.new(opts_b)

# Reverse order: Beta before Alpha
var struct_beta2 = codegen.LeanStructure.new("Beta")
struct_beta2 = struct_beta2.add_field("y", "Int")
var struct_alpha2 = codegen.LeanStructure.new("Alpha")
struct_alpha2 = struct_alpha2.add_field("x", "Int")

cg_b = cg_b.add_structure(struct_beta2)
cg_b = cg_b.add_structure(struct_alpha2)

# Reverse order: mul before add
var func_mul2 = codegen.LeanFunction.new("mul")
func_mul2 = func_mul2.add_param("b", "Nat")
func_mul2 = func_mul2.with_return_type("Nat")
func_mul2 = func_mul2.with_body("b")
var func_add2 = codegen.LeanFunction.new("add")
func_add2 = func_add2.add_param("a", "Nat")
func_add2 = func_add2.with_return_type("Nat")
func_add2 = func_add2.with_body("a")

cg_b = cg_b.add_function(func_mul2)
cg_b = cg_b.add_function(func_add2)

# Reverse order: mul_comm before add_comm
var thm_b2 = codegen.LeanTheorem.new("mul_comm", "a * b = b * a")
var thm_a2 = codegen.LeanTheorem.new("add_comm", "a + b = b + a")
cg_b = cg_b.add_theorem(thm_b2)
cg_b = cg_b.add_theorem(thm_a2)

val output_b = cg_b.emit()

# Both must be identical
expect(output_a).to_equal(output_b)
```

</details>

#### sorts inductives deterministically in emit()

- sorts inductives deterministically in emit()
   - Expected: out1 equals `out2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sorts inductives deterministically in emit()")
var opts = codegen.LeanCodegenOptions.new()
opts = opts.with_module_name("IndTest")

# Codegen with Z before A
var cg1 = codegen.LeanCodegen.new(opts)
var ind_z = codegen.LeanInductive.new("Zebra")
ind_z = ind_z.add_constructor("Striped", [])
var ind_a = codegen.LeanInductive.new("Ant")
ind_a = ind_a.add_constructor("Worker", [])
cg1 = cg1.add_inductive(ind_z)
cg1 = cg1.add_inductive(ind_a)
val out1 = cg1.emit()

# Codegen with A before Z
var cg2 = codegen.LeanCodegen.new(opts)
var ind_a2 = codegen.LeanInductive.new("Ant")
ind_a2 = ind_a2.add_constructor("Worker", [])
var ind_z2 = codegen.LeanInductive.new("Zebra")
ind_z2 = ind_z2.add_constructor("Striped", [])
cg2 = cg2.add_inductive(ind_a2)
cg2 = cg2.add_inductive(ind_z2)
val out2 = cg2.emit()

expect(out1).to_equal(out2)
```

</details>

#### generate() determinism

#### produces identical generate() output regardless of insertion order

- produces identical generate() output regardless of insertion order
   - Expected: gen_a equals `gen_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces identical generate() output regardless of insertion order")
var opts_a = codegen.LeanCodegenOptions.new()
opts_a = opts_a.with_module_name("GenTest")
var cg_a = codegen.LeanCodegen.new(opts_a)

var s1 = codegen.LeanStructure.new("Config")
s1 = s1.add_field("name", "String")
var s2 = codegen.LeanStructure.new("App")
s2 = s2.add_field("id", "Nat")

cg_a = cg_a.add_structure(s1)
cg_a = cg_a.add_structure(s2)

var f1 = codegen.LeanFunction.new("run")
f1 = f1.with_return_type("Unit")
f1 = f1.with_body("()")
var f2 = codegen.LeanFunction.new("init")
f2 = f2.with_return_type("Unit")
f2 = f2.with_body("()")

cg_a = cg_a.add_function(f1)
cg_a = cg_a.add_function(f2)

val gen_a = cg_a.generate()

# Same items, opposite order
var opts_b = codegen.LeanCodegenOptions.new()
opts_b = opts_b.with_module_name("GenTest")
var cg_b = codegen.LeanCodegen.new(opts_b)

var s2b = codegen.LeanStructure.new("App")
s2b = s2b.add_field("id", "Nat")
var s1b = codegen.LeanStructure.new("Config")
s1b = s1b.add_field("name", "String")

cg_b = cg_b.add_structure(s2b)
cg_b = cg_b.add_structure(s1b)

var f2b = codegen.LeanFunction.new("init")
f2b = f2b.with_return_type("Unit")
f2b = f2b.with_body("()")
var f1b = codegen.LeanFunction.new("run")
f1b = f1b.with_return_type("Unit")
f1b = f1b.with_body("()")

cg_b = cg_b.add_function(f2b)
cg_b = cg_b.add_function(f1b)

val gen_b = cg_b.generate()

expect(gen_a).to_equal(gen_b)
```

</details>

#### import sorting

#### sorts imports alphabetically in emit()

- sorts imports alphabetically in emit()
   - Expected: aesop_pos < mathlib_basic_pos is true
   - Expected: mathlib_basic_pos < mathlib_tactic_pos is true
   - Expected: mathlib_tactic_pos < std_pos is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sorts imports alphabetically in emit()")
var opts = codegen.LeanCodegenOptions.new()
opts = opts.with_module_name("ImportTest")
var cg = codegen.LeanCodegen.new(opts)

# Add imports in non-alphabetical order
cg = cg.add_import("Std.Data.List")
cg = cg.add_import("Aesop")
cg = cg.add_import("Mathlib.Tactic")

val output = cg.generate()

# Verify Aesop comes before Mathlib which comes before Std
val aesop_pos = output.find("import Aesop")
val mathlib_basic_pos = output.find("import Mathlib.Data.Nat.Basic")
val mathlib_tactic_pos = output.find("import Mathlib.Tactic")
val std_pos = output.find("import Std.Data.List")

# Aesop should come first (alphabetically before Mathlib)
expect(aesop_pos < mathlib_basic_pos).to_equal(true)
# Mathlib.Data should come before Mathlib.Tactic
expect(mathlib_basic_pos < mathlib_tactic_pos).to_equal(true)
# Mathlib.Tactic should come before Std
expect(mathlib_tactic_pos < std_pos).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `bc6e906c975a60edfff4ed86dc68be34d607a6efeb35b8edce8a3a752809d154`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc6e906c975a60edfff4ed86dc68be34d607a6efeb35b8edce8a3a752809d154`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc6e906c975a60edfff4ed86dc68be34d607a6efeb35b8edce8a3a752809d154`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/verification/deterministic_emission_spec.spl
mirror: doc/06_spec/01_unit/compiler/verification/deterministic_emission_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/verification/deterministic_emission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/verification/deterministic_emission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/verification/deterministic_emission_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces identical output regardless of insertion order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/deterministic_emission_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sorts inductives deterministically in emit()' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/verification/deterministic_emission_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces identical generate() output regardless of insertion order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
