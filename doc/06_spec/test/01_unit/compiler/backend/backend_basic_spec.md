# Backend Basic Specification

> <details>

<!-- sdn-diagram:id=backend_basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_basic_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Basic Specification

## Scenarios

### Backend Basic

#### creates a builder with default metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = new_builder("basic")

expect(builder.test_name).to_equal("basic")
expect(builder.instructions.len()).to_equal(0)
expect(builder.next_vreg).to_equal(0)
```

</details>

#### tracks registers and preserves backend selection

1. builder add const int
2. builder add const int
3. builder add add
4. builder only backend
   - Expected: builder.next_vreg equals `5`
   - Expected: test_case.name equals `tracked`
   - Expected: test_case.instructions.len() equals `3`
   - Expected: test_case.expected_backends.len() equals `1`
   - Expected: test_case.expected_backends[0] equals `BackendTarget.Interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = new_builder("tracked")
builder.add_const_int(0, 42)
builder.add_const_int(3, 7)
builder.add_add(4, 0, 3)
builder.only_backend(BackendTarget.Interpreter)

val test_case = builder.build()

expect(builder.next_vreg).to_equal(5)
expect(test_case.name).to_equal("tracked")
expect(test_case.instructions.len()).to_equal(3)
expect(test_case.expected_backends.len()).to_equal(1)
expect(test_case.expected_backends[0]).to_equal(BackendTarget.Interpreter)
```

</details>

#### builds the canned arithmetic helper

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_case = simple_arithmetic()

expect(test_case.name).to_equal("simple_arithmetic")
expect(test_case.instructions.len()).to_equal(4)
expect(test_case.expected_backends.len()).to_equal(3)
expect(test_case.expected_backends[0]).to_equal(BackendTarget.Cranelift)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/backend_basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Backend Basic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
