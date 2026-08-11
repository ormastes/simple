# Lazy Val Specification

> <details>

<!-- sdn-diagram:id=lazy_val_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lazy_val_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lazy_val_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lazy_val_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lazy Val Specification

## Scenarios

### Lazy Val

#### keeps lazy value states and errors available

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = lazy_val_source()

expect(source).to_contain("enum LazyStatus:")
expect(source).to_contain("class LazyState:")
expect(source).to_contain("class LazyError:")
expect(source).to_contain("fn lazy_state_is_pending(s: LazyState) -> bool")
expect(source).to_contain("fn lazy_error_message(err: LazyError) -> text")
```

</details>

#### keeps lazy force memoization and mapping APIs available

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = lazy_val_source()

expect(source).to_contain("class Lazy:")
expect(source).to_contain("me force()")
expect(source).to_contain("me force_or_default(default_val)")
expect(source).to_contain("fn map(f: fn()) -> Lazy")
expect(source).to_contain("fn flat_map(f: fn()) -> Lazy")
expect(source).to_contain("static fn new(thunk: fn()) -> Lazy")
expect(source).to_contain("class Memo:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/interpreter/lazy_val_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lazy Val

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
