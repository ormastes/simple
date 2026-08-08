# Robust Lifecycle Persistence Model

> This scenario manual proves the lifecycle-persistence model is ordinary Simple data. It validates lifecycle ordering, rejects unsafe dependency direction, and fails closed when transition or recovery metadata is incomplete.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Robust Lifecycle Persistence Model

This scenario manual proves the lifecycle-persistence model is ordinary Simple data. It validates lifecycle ordering, rejects unsafe dependency direction, and fails closed when transition or recovery metadata is incomplete.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/robust_lifecycle_persistence.md |
| Plan | doc/03_plan/sys_test/robust_lifecycle_persistence.md |
| Design | doc/05_design/language/lifecycle/robust_lifecycle_persistence_design_2026-08-04.md |
| Research | doc/01_research/domain/language/lifecycle/robust_lifecycle_persistence_research_synthesis_2026-08-04.md |
| Source | `test/03_system/feature/language/robust_lifecycle_persistence_spec.spl` |
| Updated | 2026-08-04 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This scenario manual proves the lifecycle-persistence model is ordinary Simple
data. It validates lifecycle ordering, rejects unsafe dependency direction, and
fails closed when transition or recovery metadata is incomplete.

The selected design intentionally adds no `life`, `virtual life`, `transition`,
or `recovery` source declarations. Products construct typed values with normal
Simple functions, structs, arrays, enums, and direct constructors.

## Requirements

**Requirements:** doc/02_requirements/feature/robust_lifecycle_persistence.md

Covered requirements:

- REQ-004: lifecycle order is an acyclic directed graph.
- REQ-005: a strong dependency survives at least as long as its owner.
- REQ-006: transition and recovery policies are typed library values.
- REQ-012: focused executable evidence covers all initial validators.

## Plan

**Plan:** doc/03_plan/sys_test/robust_lifecycle_persistence.md

## Design

**Design:** doc/05_design/language/lifecycle/robust_lifecycle_persistence_design_2026-08-04.md

## Research

**Research:** doc/01_research/domain/language/lifecycle/robust_lifecycle_persistence_research_synthesis_2026-08-04.md

## Syntax

Run the focused scenario with the repository-managed pure-Simple binary:

```sh
bin/simple test test/03_system/feature/language/robust_lifecycle_persistence_spec.spl --mode=interpreter
```

## Scenario contract

The primary flow defines four ordered levels: call, process, warm boot, and
power loss. A path from a shorter level to a longer level means the latter
survives every boundary represented by the former.

The dependency scenario checks both directions. Process state may depend on
power-loss state, while power-loss state may not strongly depend on process
state.

Malformed graph evidence includes duplicate level IDs and a two-node cycle.
The validator returns stable typed codes instead of silently accepting either
shape.

Transition evidence binds a known boundary and non-empty volatile, retained,
persistent, environment, and restart policies. Recovery evidence binds a
positive schema plus codec, validation, migration, recovery, clean-start,
reconciliation, and activation functions.

## Expected results

- The ordered graph validates.
- Transitive reachability resolves call through power loss.
- Reverse lifecycle dependency is rejected.
- Duplicate IDs report `DuplicateLevelId`.
- Cycles report `Cycle`.
- Missing transition policy reports `EmptyTransitionField`.
- Non-positive recovery schema reports `InvalidSchema`.

## Failure diagnostics

If graph validation fails, inspect level IDs before edges because duplicate and
empty-level errors are reported first. If transition or recovery validation
fails, preserve the returned code and detail in product diagnostics; do not
replace it with a generic fallback.

## Operator interpretation

Treat `valid=true` as admission to the next integration layer, not as proof that
the product has persisted bytes. A product must still bind the validated model
to a real codec, storage backend, linker region, boot entry, and restart test.

When adding a lifecycle level, update the graph and every product transition
that crosses it. When changing a recovery schema, keep the previous decoder and
migration path available for every supported deployed version.

Do not persist a direct pointer, runtime `+T` handle, or the repository's
snapshot-local `EntityRef` as reboot-stable identity. Use the durable identity
owner and validate compatibility during activation.

## Review checklist

- Level identifiers are unique and names are non-empty.
- Every edge endpoint exists in the same graph.
- The graph remains acyclic after adding a level or edge.
- Strong dependencies point toward equal-or-longer survival.
- Transition policy fields name real platform-owned policies.
- Recovery schema is positive and every function binding is present.
- Product evidence distinguishes model validation from persistence execution.

## Evidence boundary

The scenarios do not claim storage crash consistency, reboot execution, linker
placement, device-origin power-cut evidence, or formal proof evidence. Those are
separate product and platform lanes.

## Scenarios

### Robust lifecycle persistence metadata

#### accepts an ordered lifecycle graph

- Define an ordered lifecycle graph
- Resolve transitive survival order


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Define an ordered lifecycle graph")
val graph = ordered_graph()
val result = lifecycle_graph_validate(graph)
expect(result.valid).to_be(true)
step("Resolve transitive survival order")
expect(lifecycle_reaches(graph, LIFE_CALL, LIFE_POWER_LOSS)).to_be(true)
```

</details>

#### rejects an unsafe lifecycle dependency

- Accept a dependency that survives longer than its owner
- Reject a dependency that expires before its owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = ordered_graph()
step("Accept a dependency that survives longer than its owner")
expect(lifecycle_dependency_allowed(graph, LIFE_PROCESS, LIFE_POWER_LOSS)).to_be(true)
step("Reject a dependency that expires before its owner")
expect(lifecycle_dependency_allowed(graph, LIFE_POWER_LOSS, LIFE_PROCESS)).to_be(false)
```

</details>

#### rejects malformed lifecycle graphs

- Reject duplicate lifecycle identifiers
   - Expected: duplicate_result.code equals `LifecycleValidationCode.DuplicateLevelId`
- Reject a lifecycle cycle
   - Expected: cycle_result.code equals `LifecycleValidationCode.Cycle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject duplicate lifecycle identifiers")
val duplicate_result = lifecycle_graph_validate(duplicate_graph())
expect(duplicate_result.valid).to_be(false)
expect(duplicate_result.code).to_equal(LifecycleValidationCode.DuplicateLevelId)

step("Reject a lifecycle cycle")
val cycle_result = lifecycle_graph_validate(cyclic_graph())
expect(cycle_result.valid).to_be(false)
expect(cycle_result.code).to_equal(LifecycleValidationCode.Cycle)
```

</details>

#### validates transition and recovery metadata

- Validate transition and recovery metadata
- Reject an incomplete transition
   - Expected: incomplete_result.code equals `LifecycleValidationCode.EmptyTransitionField`
- Reject a non-positive recovery schema
   - Expected: invalid_recovery_result.code equals `LifecycleValidationCode.InvalidSchema`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val graph = ordered_graph()
step("Validate transition and recovery metadata")
val transition_result = lifecycle_transition_validate(graph, valid_transition())
val recovery_result = recovery_registration_validate(graph, valid_recovery())
expect(transition_result.valid).to_be(true)
expect(recovery_result.valid).to_be(true)

step("Reject an incomplete transition")
val incomplete_result = lifecycle_transition_validate(graph, incomplete_transition())
expect(incomplete_result.valid).to_be(false)
expect(incomplete_result.code).to_equal(LifecycleValidationCode.EmptyTransitionField)

step("Reject a non-positive recovery schema")
val invalid_recovery_result = recovery_registration_validate(graph, invalid_schema_recovery())
expect(invalid_recovery_result.valid).to_be(false)
expect(invalid_recovery_result.code).to_equal(LifecycleValidationCode.InvalidSchema)
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


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/robust_lifecycle_persistence.md`
- **Plan:** `doc/03_plan/sys_test/robust_lifecycle_persistence.md`
- **Design:** `doc/05_design/language/lifecycle/robust_lifecycle_persistence_design_2026-08-04.md`
- **Research:** `doc/01_research/domain/language/lifecycle/robust_lifecycle_persistence_research_synthesis_2026-08-04.md`


</details>
