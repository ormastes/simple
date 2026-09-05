# Deterministic Lean Emission Specification

> Verifies that LeanCodegen produces byte-identical output regardless of the order in which items (structures, inductives, functions, theorems, imports) are added. Both `emit()` and `generate()` must sort by `.name` before rendering.

<!-- sdn-diagram:id=deterministic_emission_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=deterministic_emission_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

deterministic_emission_spec -> verification
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=deterministic_emission_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/00_formal_verification/compiler/deterministic_emission_spec.spl` |
| Updated | 2026-06-01 |
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

1. var opts a = codegen LeanCodegenOptions new
2. opts a = opts a with module name
3. var cg a = codegen LeanCodegen new
4. var struct alpha = codegen LeanStructure new
5. struct alpha = struct alpha add field
6. var struct beta = codegen LeanStructure new
7. struct beta = struct beta add field
8. cg a = cg a add structure
9. cg a = cg a add structure
10. var func add = codegen LeanFunction new
11. func add = func add add param
12. func add = func add with return type
13. func add = func add with body
14. var func mul = codegen LeanFunction new
15. func mul = func mul add param
16. func mul = func mul with return type
17. func mul = func mul with body
18. cg a = cg a add function
19. cg a = cg a add function
20. var thm a = codegen LeanTheorem new
21. var thm b = codegen LeanTheorem new
22. cg a = cg a add theorem
23. cg a = cg a add theorem
24. var opts b = codegen LeanCodegenOptions new
25. opts b = opts b with module name
26. var cg b = codegen LeanCodegen new
27. var struct beta2 = codegen LeanStructure new
28. struct beta2 = struct beta2 add field
29. var struct alpha2 = codegen LeanStructure new
30. struct alpha2 = struct alpha2 add field
31. cg b = cg b add structure
32. cg b = cg b add structure
33. var func mul2 = codegen LeanFunction new
34. func mul2 = func mul2 add param
35. func mul2 = func mul2 with return type
36. func mul2 = func mul2 with body
37. var func add2 = codegen LeanFunction new
38. func add2 = func add2 add param
39. func add2 = func add2 with return type
40. func add2 = func add2 with body
41. cg b = cg b add function
42. cg b = cg b add function
43. var thm b2 = codegen LeanTheorem new
44. var thm a2 = codegen LeanTheorem new
45. cg b = cg b add theorem
46. cg b = cg b add theorem
   - Expected: output_a equals `output_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 69 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var opts = codegen LeanCodegenOptions new
2. opts = opts with module name
3. var cg1 = codegen LeanCodegen new
4. var ind z = codegen LeanInductive new
5. ind z = ind z add constructor
6. var ind a = codegen LeanInductive new
7. ind a = ind a add constructor
8. cg1 = cg1 add inductive
9. cg1 = cg1 add inductive
10. var cg2 = codegen LeanCodegen new
11. var ind a2 = codegen LeanInductive new
12. ind a2 = ind a2 add constructor
13. var ind z2 = codegen LeanInductive new
14. ind z2 = ind z2 add constructor
15. cg2 = cg2 add inductive
16. cg2 = cg2 add inductive
   - Expected: out1 equals `out2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var opts a = codegen LeanCodegenOptions new
2. opts a = opts a with module name
3. var cg a = codegen LeanCodegen new
4. var s1 = codegen LeanStructure new
5. s1 = s1 add field
6. var s2 = codegen LeanStructure new
7. s2 = s2 add field
8. cg a = cg a add structure
9. cg a = cg a add structure
10. var f1 = codegen LeanFunction new
11. f1 = f1 with return type
12. f1 = f1 with body
13. var f2 = codegen LeanFunction new
14. f2 = f2 with return type
15. f2 = f2 with body
16. cg a = cg a add function
17. cg a = cg a add function
18. var opts b = codegen LeanCodegenOptions new
19. opts b = opts b with module name
20. var cg b = codegen LeanCodegen new
21. var s2b = codegen LeanStructure new
22. s2b = s2b add field
23. var s1b = codegen LeanStructure new
24. s1b = s1b add field
25. cg b = cg b add structure
26. cg b = cg b add structure
27. var f2b = codegen LeanFunction new
28. f2b = f2b with return type
29. f2b = f2b with body
30. var f1b = codegen LeanFunction new
31. f1b = f1b with return type
32. f1b = f1b with body
33. cg b = cg b add function
34. cg b = cg b add function
   - Expected: gen_a equals `gen_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var opts = codegen LeanCodegenOptions new
2. opts = opts with module name
3. var cg = codegen LeanCodegen new
4. cg = cg add import
5. cg = cg add import
6. cg = cg add import
   - Expected: aesop_pos < mathlib_basic_pos is true
   - Expected: mathlib_basic_pos < mathlib_tactic_pos is true
   - Expected: mathlib_tactic_pos < std_pos is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
