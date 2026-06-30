# Sandbox Configuration Specification

> Sandbox configuration parsing for resource-constrained execution environments.

<!-- sdn-diagram:id=sandbox_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sandbox_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sandbox_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sandbox_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sandbox Configuration Specification

Sandbox configuration parsing for resource-constrained execution environments.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #3130 |
| Category | Tooling |
| Status | In Progress |
| Source | `test/01_unit/app/tooling/sandbox_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Sandbox configuration parsing for resource-constrained execution environments.
Supports memory limits (K/M/G suffixes), time limits, network isolation, and
domain whitelisting for secure script execution.

## Scenarios

### sandbox module compilation

#### compiles successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

### memory size parsing logic

#### validates K suffix calculation

#### 512K should be 512 * 1024

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = 512 * 1024
expect expected == 524288
```

</details>

#### validates M suffix calculation

#### 256M should be 256 * 1024 * 1024

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = 256 * 1024 * 1024
expect expected == 268435456
```

</details>

#### validates G suffix calculation

#### 2G should be 2 * 1024 * 1024 * 1024

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected = 2 * 1024 * 1024 * 1024
expect expected == 2147483648
```

</details>

### sandbox configuration patterns

#### validates boolean defaults

#### false is the default for flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_flag = false
expect default_flag == false
```

</details>

### sandbox flag detection logic

#### validates --sandbox flag

#### matches sandbox flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect flag == "--sandbox"
```

</details>

#### validates --no-network flag

#### matches no-network flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect flag == "--no-network"
```

</details>

#### validates --time-limit flag

#### matches time-limit flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect flag == "--time-limit"
```

</details>

#### validates --memory-limit flag

#### matches memory-limit flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect flag == "--memory-limit"
```

</details>

### string suffix detection

#### validates G suffix

#### ends with G

1. expect value ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect value.ends_with("G") == true
```

</details>

#### validates M suffix

#### ends with M

1. expect value ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect value.ends_with("M") == true
```

</details>

#### validates K suffix

#### ends with K

1. expect value ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect value.ends_with("K") == true
```

</details>

### comma-separated parsing logic

#### validates split on comma

#### splits into 3 parts

1. expect parts len


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parts.len() == 3
```

</details>

#### first part is example.com

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parts[0] == "example.com"
```

</details>

#### second part is test.org

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parts[1] == "test.org"
```

</details>

#### third part is foo.net

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect parts[2] == "foo.net"
```

</details>

### trim whitespace logic

#### validates trim

#### trims whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect trimmed == "512M"
```

</details>

### sandbox configuration concepts

#### demonstrates mutable config pattern

#### allows field mutation

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect config_modified == true
```

</details>

#### demonstrates Option usage - Some

#### has value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect some_val == 60
```

</details>

#### demonstrates Option usage - None

#### validates None concept

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val none_val: Option<i64> = nil
expect(none_val).to_be_nil()
```

</details>

### argument iteration pattern

#### validates while loop counter

#### iterates 5 times

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect count == 5
```

</details>

#### validates index bounds checking

#### checks bounds correctly

1. expect i + 1 < args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect i + 1 < args.len() == true
```

</details>

### flag value parsing pattern

#### validates increment for value flags

#### increments by 2 for value flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect i == 2
```

</details>

### builder pattern validation

#### validates method chaining concept

#### chains operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect value == 30
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
