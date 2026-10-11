# Text Partition Lowering Specification

> Tests covering REQ-PARTITION-001 primitive text partition MIR.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Partition Lowering Specification

## Scenarios

### REQ-PARTITION-001 primitive text partition MIR

#### should select first and last partition providers for typed text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (mir, errors) = lower_partition_source("fn first(value: text, separator: text) -> [text]:\n    value.partition(separator)\nfn last(value: text, separator: text) -> [text]:\n    value.rpartition(separator)\n")
expect(errors.len()).to_equal(0)
expect(mir).to_contain("rt_string_partition")
expect(mir).to_contain("rt_string_rpartition")
```

</details>

#### should preserve an instance method named partition

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (mir, errors) = lower_partition_source("struct LocalPartition:\n    value: i64\nimpl LocalPartition:\n    fn partition(self, separator: text) -> i64: self.value\nfn invoke(value: LocalPartition) -> i64:\n    value.partition(\"=\")\n")
expect(errors.len()).to_equal(0)
expect(mir).to_contain("LocalPartition")
expect(mir.contains("rt_string_partition")).to_equal(false)
```

</details>

#### should report a text separator diagnostic for a numeric argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (mir, errors) = lower_partition_source("fn invalid() -> i64:\n    val result = \"a=b\".partition(1)\n    0\n")
expect(errors.len()).to_equal(1)
expect(errors[0]).to_contain("text.partition expects a text separator")
expect(mir.contains("rt_string_partition")).to_equal(false)
```

</details>

#### should reject a numeric receiver without choosing a text provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (mir, errors) = lower_partition_source("fn invalid() -> i64:\n    val result = 7.partition(\"=\")\n    0\n")
expect(errors.len()).to_equal(1)
expect(errors[0]).to_contain("unresolved method call: partition")
expect(mir.contains("rt_string_partition")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/text_partition_lowering_spec.spl` |
| Updated | 2026-10-09 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REQ-PARTITION-001 primitive text partition MIR.
- REQ-PARTITION-001 primitive text partition MIR

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
