# Suspension Operator (`~`) Specification

The `~` operator marks expressions that may suspend (perform async operations). It appears in three contexts:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #270-275 |
| Status | Draft |
| Source | `/home/ormastes/dev/pub/simple/test/specs/suspension_operator_spec.spl` |
| Updated | 2026-03-29 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 0 |
| Slow scenarios | 0 |
| Skipped scenarios | 24 |
| Pending scenarios | 0 |

**Keywords:** async, suspension, await, effects, concurrency
**Last Updated:** 2026-01-05
**Topics:** concurrency, syntax, effects
**Migrated From:** doc/06_spec/suspension_operator.md

## Overview

The `~` operator marks expressions that may suspend (perform async operations). It appears in three contexts:

| Context | Syntax | Meaning |
|---------|--------|---------|
| Assignment | `x ~= expr` | Evaluate `expr` (may suspend), assign result to `x` |
| If guard | `if~ cond:` | Evaluate `cond` (may suspend), branch on result |
| While guard | `while~ cond:` | Evaluate `cond` each iteration (may suspend) |

---

## Related Specifications

- **Async Default** - Async-by-default function model
- **Concurrency** - Async/await, futures, actors
- **Syntax** - Core language syntax
- **Functions** - Function definitions and effects

## Scenarios

- [skip] motivation_1
- [skip] syntax_2
- [skip] syntax_3
- [skip] syntax_4
- [skip] syntax_5
- [skip] effect_system_integration_6
- [skip] effect_system_integration_7
- [skip] effect_system_integration_8
- [skip] interaction_with_existing_constructs_9
- [skip] interaction_with_existing_constructs_10
- [skip] interaction_with_existing_constructs_11
- [skip] interaction_with_existing_constructs_12
- [skip] examples_13
- [skip] examples_14
- [skip] examples_15
- [skip] examples_16
- [skip] examples_17
- [skip] examples_18
- [skip] compound_suspending_assignment_19
- [skip] chained_suspending_conditions_20
- [skip] implementation_notes_21
- [skip] implementation_notes_22
- [skip] migration_guide_23
- [skip] migration_guide_24
