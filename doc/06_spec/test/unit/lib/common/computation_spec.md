# Computation Specification

> <details>

<!-- sdn-diagram:id=computation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=computation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

computation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=computation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Computation Specification

## Scenarios

### Computation Expression protocol

### CE builder name constants

#### CE_BUILDER_RESULT is result_ce

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CE_BUILDER_RESULT).to_equal("result_ce")
```

</details>

#### CE_BUILDER_OPTION is option_ce

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CE_BUILDER_OPTION).to_equal("option_ce")
```

</details>

#### CE_BUILDER_SEQ is seq_ce

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CE_BUILDER_SEQ).to_equal("seq_ce")
```

</details>

### ce_builder_known

#### recognizes result_ce builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_builder_known("result_ce")).to_equal(true)
```

</details>

#### recognizes option_ce builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_builder_known("option_ce")).to_equal(true)
```

</details>

#### recognizes seq_ce builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_builder_known("seq_ce")).to_equal(true)
```

</details>

#### does not recognize unknown builder name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_builder_known("unknown_ce")).to_equal(false)
```

</details>

#### does not recognize empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_builder_known("")).to_equal(false)
```

</details>

#### recognizes CE_BUILDER_RESULT constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_builder_known(CE_BUILDER_RESULT)).to_equal(true)
```

</details>

#### recognizes CE_BUILDER_OPTION constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_builder_known(CE_BUILDER_OPTION)).to_equal(true)
```

</details>

#### recognizes CE_BUILDER_SEQ constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_builder_known(CE_BUILDER_SEQ)).to_equal(true)
```

</details>

#### does not recognize partial name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_builder_known("result")).to_equal(false)
```

</details>

#### is case sensitive for unknown names

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_builder_known("Result_ce")).to_equal(false)
```

</details>

### ce_bind_fn_name

#### returns bind name for result_ce

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_bind_fn_name("result_ce")).to_equal("result_ce_bind")
```

</details>

#### returns bind name for option_ce

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_bind_fn_name("option_ce")).to_equal("option_ce_bind")
```

</details>

#### returns bind name for seq_ce

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_bind_fn_name("seq_ce")).to_equal("seq_ce_bind")
```

</details>

#### returns bind name for arbitrary builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_bind_fn_name("my_ce")).to_equal("my_ce_bind")
```

</details>

#### bind name uses builder_bind pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = ce_bind_fn_name("foo_ce")
expect(name).to_end_with("_bind")
```

</details>

#### bind name starts with builder name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = ce_bind_fn_name("foo_ce")
expect(name).to_start_with("foo_ce")
```

</details>

### ce_return_fn_name

#### returns return name for result_ce

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_return_fn_name("result_ce")).to_equal("result_ce_return")
```

</details>

#### returns return name for option_ce

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_return_fn_name("option_ce")).to_equal("option_ce_return")
```

</details>

#### returns return name for seq_ce

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_return_fn_name("seq_ce")).to_equal("seq_ce_return")
```

</details>

#### returns return name for arbitrary builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_return_fn_name("my_ce")).to_equal("my_ce_return")
```

</details>

#### return name ends with _return

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = ce_return_fn_name("foo_ce")
expect(name).to_end_with("_return")
```

</details>

#### return name starts with builder name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = ce_return_fn_name("foo_ce")
expect(name).to_start_with("foo_ce")
```

</details>

### ce_zero_fn_name

#### returns zero name for result_ce

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_zero_fn_name("result_ce")).to_equal("result_ce_zero")
```

</details>

#### returns zero name for option_ce

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_zero_fn_name("option_ce")).to_equal("option_ce_zero")
```

</details>

#### returns zero name for seq_ce

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_zero_fn_name("seq_ce")).to_equal("seq_ce_zero")
```

</details>

#### returns zero name for arbitrary builder

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_zero_fn_name("my_ce")).to_equal("my_ce_zero")
```

</details>

#### zero name ends with _zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = ce_zero_fn_name("foo_ce")
expect(name).to_end_with("_zero")
```

</details>

#### zero name starts with builder name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = ce_zero_fn_name("foo_ce")
expect(name).to_start_with("foo_ce")
```

</details>

### naming convention consistency

#### all three names use the same prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = "test_ce"
val bind_name = ce_bind_fn_name(builder)
val return_name = ce_return_fn_name(builder)
val zero_name = ce_zero_fn_name(builder)
expect(bind_name).to_start_with("test_ce")
```

</details>

#### bind and return names share builder prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = "state_ce"
val bind_name = ce_bind_fn_name(builder)
val return_name = ce_return_fn_name(builder)
expect(bind_name).to_start_with("state_ce")
```

</details>

#### bind and zero names share builder prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = "async_ce"
val bind_name = ce_bind_fn_name(builder)
val zero_name = ce_zero_fn_name(builder)
expect(zero_name).to_start_with("async_ce")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/computation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Computation Expression protocol
- CE builder name constants
- ce_builder_known
- ce_bind_fn_name
- ce_return_fn_name
- ce_zero_fn_name
- naming convention consistency

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
