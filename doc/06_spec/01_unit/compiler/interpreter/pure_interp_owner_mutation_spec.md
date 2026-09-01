# Pure Interp Owner Mutation Specification

> Tests covering pure-Simple core interpreter mutates collections through the owner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pure Interp Owner Mutation Specification

## Scenarios

### pure-Simple core interpreter mutates collections through the owner

#### upsert appends to both parallel arrays and set_field_idx writes in place

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- upsert appends to both parallel arrays and set_field_idx writes in place
   - Expected: val_get_int(val_struct_get_field(d, "a")) equals `3`
   - Expected: val_get_int(val_struct_get_field(d, "b")) equals `2`
   - Expected: val_get_int(val_struct_get_field(d, "b")) equals `9`
   - Expected: val_get_int(val_struct_get_field(d, "b")) equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("upsert appends to both parallel arrays and set_field_idx writes in place")
val_reset()
val d = val_make_struct("__dict", [], [])
val_struct_upsert_field(d, "a", val_make_int(1))
val_struct_upsert_field(d, "b", val_make_int(2))
val_struct_upsert_field(d, "a", val_make_int(3))
expect(val_get_int(val_struct_get_field(d, "a"))).to_equal(3)
expect(val_get_int(val_struct_get_field(d, "b"))).to_equal(2)
val_struct_set_field_idx(d, 1, val_make_int(9))
expect(val_get_int(val_struct_get_field(d, "b"))).to_equal(9)
# out-of-range index is a no-op, not a crash
val_struct_set_field_idx(d, 7, val_make_int(0))
expect(val_get_int(val_struct_get_field(d, "b"))).to_equal(9)
```

</details>

#### two structs never share a values array after owner mutation

- two structs never share a values array after owner mutation
   - Expected: val_get_int(val_struct_get_field(a, "x")) equals `5`
   - Expected: val_get_int(val_struct_get_field(b, "x")) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("two structs never share a values array after owner mutation")
val_reset()
val a = val_make_struct("S", ["x"], [val_make_int(1)])
val b = val_make_struct("S", ["x"], [val_make_int(1)])
val_struct_set_field_idx(a, 0, val_make_int(5))
expect(val_get_int(val_struct_get_field(a, "x"))).to_equal(5)
expect(val_get_int(val_struct_get_field(b, "x"))).to_equal(1)
```

</details>

#### value.spl primitives do not write back through a temp alias

- value.spl primitives do not write back through a temp alias
   - Expected: v contains `val_struct_fields[vid].push(field_name)`
   - Expected: v contains `val_struct_values[vid][idx] = new_val`
   - Expected: v does not contain `val_struct_values[vid] = values`
   - Expected: v does not contain `val_struct_fields[vid] = fields`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("value.spl primitives do not write back through a temp alias")
val v = src("value.spl")
expect(v.contains("val_struct_fields[vid].push(field_name)")).to_equal(true)
expect(v.contains("val_struct_values[vid][idx] = new_val")).to_equal(true)
expect(v.contains("val_struct_values[vid] = values")).to_equal(false)
expect(v.contains("val_struct_fields[vid] = fields")).to_equal(false)
```

</details>

#### index-assign and push evaluators mutate val_arrays in place

- index-assign and push evaluators mutate val_arrays in place
   - Expected: access contains `val_arrays[base_val][idx] = new_val`
   - Expected: access does not contain `val_arrays[base_val] = elements`
   - Expected: assign contains `val_arrays[base_val][idx] = new_val`
   - Expected: assign contains `val_arrays[ix_base][ix_i] = ix_new`
   - Expected: assign does not contain `val_arrays[ix_base] = ix_elems`
   - Expected: call contains `val_arrays[receiver].push(new_elem)`
   - Expected: call does not contain `val_arrays[receiver] = new_elems`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("index-assign and push evaluators mutate val_arrays in place")
val access = src("eval_access.spl")
val assign = src("_EvalOps/access_literal_assign_eval.spl")
val call = src("_EvalOps/call_method_eval.spl")
expect(access.contains("val_arrays[base_val][idx] = new_val")).to_equal(true)
expect(access.contains("val_arrays[base_val] = elements")).to_equal(false)
expect(assign.contains("val_arrays[base_val][idx] = new_val")).to_equal(true)
expect(assign.contains("val_arrays[ix_base][ix_i] = ix_new")).to_equal(true)
expect(assign.contains("val_arrays[ix_base] = ix_elems")).to_equal(false)
expect(call.contains("val_arrays[receiver].push(new_elem)")).to_equal(true)
expect(call.contains("val_arrays[receiver] = new_elems")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/pure_interp_owner_mutation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure-Simple core interpreter mutates collections through the owner.
- pure-Simple core interpreter mutates collections through the owner

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b676333e36d544fdc42f12f1a03dd27cab74f6ef0cd5837c9931ce8ad570381b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b676333e36d544fdc42f12f1a03dd27cab74f6ef0cd5837c9931ce8ad570381b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b676333e36d544fdc42f12f1a03dd27cab74f6ef0cd5837c9931ce8ad570381b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/interpreter/pure_interp_owner_mutation_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/pure_interp_owner_mutation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/pure_interp_owner_mutation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/pure_interp_owner_mutation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/pure_interp_owner_mutation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/pure_interp_owner_mutation_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'upsert appends to both parallel arrays and set_field_idx writes in place' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/pure_interp_owner_mutation_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two structs never share a values array after owner mutation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/pure_interp_owner_mutation_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'value.spl primitives do not write back through a temp alias' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
