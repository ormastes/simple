# Method Missing Handler Specification

> Tests for the method_missing dynamic dispatch mechanism that allows objects to handle calls to undefined methods at runtime through a catch-all handler.

<!-- sdn-diagram:id=method_missing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=method_missing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

method_missing_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=method_missing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Method Missing Handler Specification

Tests for the method_missing dynamic dispatch mechanism that allows objects to handle calls to undefined methods at runtime through a catch-all handler.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Language |
| Difficulty | 3/5 |
| Status | Planned |
| Source | `test/03_system/feature/usage/method_missing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the method_missing dynamic dispatch mechanism that allows objects
to handle calls to undefined methods at runtime through a catch-all handler.

## Syntax

```simple
class DynamicHandler:
fn method_missing(name: text, args: List) -> Any:
# Handle undefined method calls
print "Called {name} with {args}"
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Dynamic Dispatch | Runtime method resolution for undefined methods |
| Method Missing | Catch-all handler for unimplemented methods |
| Reflection | Access to method name and arguments at runtime |
| Fallback Behavior | Default handling when method doesn't exist |

## Behavior

- method_missing is called when a method is not found on an object
- Receives method name and argument list as parameters
- Allows runtime behavior customization and dynamic APIs
- Can raise errors or provide default implementations
- Integration with reflection and introspection

## Related Specifications

- Dynamic Typing - Runtime type behavior
- Reflection - Introspection capabilities
- Error Handling - Exception propagation from method_missing

## Scenarios

### Method Missing Basic Handling

#### placeholder test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO[test][P2]: Implement method_missing basic tests when feature is available
expect true
```

</details>

### Method Missing with Arguments

#### placeholder test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO[test][P2]: Implement method_missing argument tests
expect true
```

</details>

### Method Missing Advanced Features

#### placeholder test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TODO[test][P2]: Implement advanced method_missing tests
expect true
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
