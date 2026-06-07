# Aop Proceed Specification

> <details>

<!-- sdn-diagram:id=aop_proceed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aop_proceed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aop_proceed_spec -> std
aop_proceed_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aop_proceed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aop Proceed Specification

## Scenarios

### Aop Proceed

#### starts with zero proceed calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = create_proceed_context_minimal("trace_around")
expect(ctx.was_called()).to_equal(false)
expect(ctx.call_count()).to_equal(0)
expect(ctx.has_error).to_equal(false)
```

</details>

#### records a single proceed call and verifies successfully

1. ctx mark proceed called
   - Expected: ctx.was_called() is true
   - Expected: ctx.call_count() equals `1`
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = create_proceed_context_minimal("trace_around")
ctx.mark_proceed_called()
expect(ctx.was_called()).to_equal(true)
expect(ctx.call_count()).to_equal(1)

val result = ctx.verify()
expect(result.is_ok()).to_equal(true)
```

</details>

#### fails verification when proceed is never called

1. "Around advice 'trace around' must call proceed


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = create_proceed_context_minimal("trace_around")
val result = ctx.verify()

expect(result.is_err()).to_equal(true)
val err_val = result.err.unwrap()
val err_msg = err_val.format()
expect(err_msg).to_equal(
    "Around advice 'trace_around' must call proceed() exactly once (called 0 times)"
)
```

</details>

#### fails verification when proceed is called multiple times

1. ctx mark proceed called
2. ctx mark proceed called
3. ctx mark proceed called
   - Expected: result.is_err() is true
   - Expected: ctx.call_count() equals `3`
4. "Around advice 'trace around' must call proceed


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = create_proceed_context_minimal("trace_around")
ctx.mark_proceed_called()
ctx.mark_proceed_called()
ctx.mark_proceed_called()

val result = ctx.verify()
expect(result.is_err()).to_equal(true)
expect(ctx.call_count()).to_equal(3)
val err_val = result.err.unwrap()
val err_msg = err_val.format()
expect(err_msg).to_equal(
    "Around advice 'trace_around' must call proceed() exactly once (called 3 times)"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mdsoc/aop_proceed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Aop Proceed

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
