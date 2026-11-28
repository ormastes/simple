# Reverse-index read-set from the selector AST

> Purpose: Prove that the mdsoc reverse index names a selector by its `PointcutSelectorId` and derives the descriptor fields a selector reads from the atoms of the lowered selector, not from a substring scan of the predicate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reverse-index read-set from the selector AST

Purpose: Prove that the mdsoc reverse index names a selector by its `PointcutSelectorId` and derives the descriptor fields a selector reads from the atoms of the lowered selector, not from a substring scan of the predicate.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/aop/aop_reverse_index_read_set_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that the mdsoc reverse index names a selector by its `PointcutSelectorId` and derives the descriptor fields a selector reads from the atoms of the lowered selector, not from a substring scan of the predicate.
Audience: compiler engineers who maintain aspect invalidation and the
reverse-reference tables.

Lifecycle: research doc/01_research/domain/dir_tldr_aspect.md; plan
doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md (stage AW-3);
architecture doc/04_architecture/extreme_typing_traceability.md; design
doc/05_design/compiler/cache/aspect_tldr_async_trace.md (section 3, gap G11).

## What the operator can rely on

| Predicate | Fields read | Conservative |
|---|---|---|
| `execution(* run(..))`, `run`, `run_*` | `function_name` | no |
| `@inline` | `attributes` | no |
| anything that does not lower (`module:...`, `*`, `mystery()`) | all five descriptor fields | yes |

A conservative read-set can only over-invalidate. A predicate that merely
contains the text of a field name (`module_path == app.core`) no longer gets a
narrow read-set: it does not lower, so it reads everything.

The four tables answer: which partitions a selector read, which selectors read
a field, which advice a target selected, and which targets an advice reaches.
A key that is not in a table gives an empty answer.

## Decision inventory (reverse_index.spl)

| Decision | Covering examples |
|---|---|
| lowered selector is unsupported | `module:app.*` / `run` |
| node is an attribute atom, node is another atom | `@inline` / `run` / `a & b` operator node |
| selector reads the name, reads attributes | `run` / `@inline` |
| read-set lists the field | `function_name` hit / `signature` miss |
| selector, target and advice table lookups | present key / absent key |
| build loops over rules, selections and advice names | two rules, two selections, shared advice |

## Scenarios

### Selector read-set

#### reads only the function name for a name predicate

- Derive the read-set of an execution predicate, a bare name and a boolean expression
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: read_set.fields equals `["function_name"]`
   - Expected: read_set.conservative is false
   - Expected: read_set.selector_id equals `aop_selector_id_v1("run")`
   - Expected: both.fields equals `["function_name"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Derive the read-set of an execution predicate, a bare name and a boolean expression")
# @req: REQ-ASPECT-AW3-READ-SET
val read_set = aop_selector_read_set(rule("execution(* run(..))", "audit"))
expect(read_set.fields).to_equal(["function_name"])
expect(read_set.conservative).to_equal(false)
expect(read_set.selector_id).to_equal(aop_selector_id_v1("run"))
val both = aop_selector_read_set(rule("execution(* run(..)) & !execution(* stop(..))", "audit"))
expect(both.fields).to_equal(["function_name"])
```

</details>

#### reads only the attributes for an attribute predicate

- Derive the read-set of an attribute predicate
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: read_set.fields equals `["attributes"]`
   - Expected: read_set.conservative is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Derive the read-set of an attribute predicate")
# @req: REQ-ASPECT-AW3-READ-SET
val read_set = aop_selector_read_set(rule("@inline", "trace"))
expect(read_set.fields).to_equal(["attributes"])
expect(read_set.conservative).to_equal(false)
```

</details>

#### reads every descriptor field when the predicate does not lower

- Derive the read-set of predicates that have no selector form
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: read_set.conservative is true
   - Expected: read_set.fields equals `["function_name", "module_path", "signature", "attributes", "effects"]`
   - Expected: read_set.selector_id equals `aop_selector_id_v1("module:app.*")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Derive the read-set of predicates that have no selector form")
# @req: REQ-ASPECT-AW3-READ-SET
val read_set = aop_selector_read_set(rule("module:app.*", "audit"))
expect(read_set.conservative).to_equal(true)
expect(read_set.fields).to_equal(["function_name", "module_path", "signature", "attributes", "effects"])
expect(read_set.selector_id).to_equal(aop_selector_id_v1("module:app.*"))
```

</details>

#### does not narrow the read-set of a predicate that only mentions a field name

- A predicate containing the text module_path is unsupported, not a module_path reader
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: aop_selector_read_set(rule("module_path == app.core", "audit")).conservative is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("A predicate containing the text module_path is unsupported, not a module_path reader")
# @req: REQ-ASPECT-AW3-READ-SET
expect(aop_selector_read_set(rule("module_path == app.core", "audit")).conservative).to_equal(true)
```

</details>

### Reverse tables

#### finds the selectors that read a changed field and none for an unread field

- Query the field table for the name, attribute and signature fields
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: aop_selectors_reading_field(index, "function_name") equals `[aop_selector_id_v1("run")]`
   - Expected: aop_selectors_reading_field(index, "attributes") equals `[aop_selector_id_v1("@inline")]`
   - Expected: aop_selectors_reading_field(index, "signature") equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Query the field table for the name, attribute and signature fields")
# @req: REQ-ASPECT-AW3-READ-SET
val index = sample_index()
expect(aop_selectors_reading_field(index, "function_name")).to_equal([aop_selector_id_v1("run")])
expect(aop_selectors_reading_field(index, "attributes")).to_equal([aop_selector_id_v1("@inline")])
expect(aop_selectors_reading_field(index, "signature")).to_equal([])
```

</details>

#### returns the partitions a selector read and nothing for an unknown selector

- Query the partition table by selector id
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: aop_partitions_of_selector(index, aop_selector_id_v1("@inline")) equals `["partition-b"]`
   - Expected: aop_partitions_of_selector(index, aop_selector_id_v1("run")) equals `["partition-a", "partition-b"]`
   - Expected: aop_partitions_of_selector(index, "sha256:unknown") equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Query the partition table by selector id")
# @req: REQ-ASPECT-AW3-READ-SET
val index = sample_index()
expect(aop_partitions_of_selector(index, aop_selector_id_v1("@inline"))).to_equal(["partition-b"])
expect(aop_partitions_of_selector(index, aop_selector_id_v1("run"))).to_equal(["partition-a", "partition-b"])
expect(aop_partitions_of_selector(index, "sha256:unknown")).to_equal([])
```

</details>

#### returns a target's ordered advice and nothing for an unknown target

- Query the selection table by target entity
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: aop_selection_of_target(index, "app.core::run") equals `["audit", "trace"]`
   - Expected: aop_selection_of_target(index, "app.core::stop") equals `["audit"]`
   - Expected: aop_selection_of_target(index, "app.core::missing") equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Query the selection table by target entity")
# @req: REQ-ASPECT-AW3-READ-SET
val index = sample_index()
expect(aop_selection_of_target(index, "app.core::run")).to_equal(["audit", "trace"])
expect(aop_selection_of_target(index, "app.core::stop")).to_equal(["audit"])
expect(aop_selection_of_target(index, "app.core::missing")).to_equal([])
```

</details>

#### returns every target of an advice and nothing for an unknown advice

- Query the advice table by advice function
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: aop_targets_of_advice(index, "audit") equals `["app.core::run", "app.core::stop"]`
   - Expected: aop_targets_of_advice(index, "trace") equals `["app.core::run"]`
   - Expected: aop_targets_of_advice(index, "missing") equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Query the advice table by advice function")
# @req: REQ-ASPECT-AW3-READ-SET
val index = sample_index()
expect(aop_targets_of_advice(index, "audit")).to_equal(["app.core::run", "app.core::stop"])
expect(aop_targets_of_advice(index, "trace")).to_equal(["app.core::run"])
expect(aop_targets_of_advice(index, "missing")).to_equal([])
```

</details>

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

- `REQ-ASPECT-AW3-READ-SET`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f18dac6a955e2d16d0fbac48e8436e7a540503cfa8e6386b532b5b88e7fefc28`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f18dac6a955e2d16d0fbac48e8436e7a540503cfa8e6386b532b5b88e7fefc28`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f18dac6a955e2d16d0fbac48e8436e7a540503cfa8e6386b532b5b88e7fefc28`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: 01_unit/compiler/aop/aop_reverse_index_read_set_spec.spl
mirror: doc/06_spec/01_unit/compiler/aop/aop_reverse_index_read_set_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/aop/aop_reverse_index_read_set_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/aop/aop_reverse_index_read_set_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
