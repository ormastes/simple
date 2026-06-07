# T32 Types Specification

> <details>

<!-- sdn-diagram:id=t32_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_types_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Types Specification

## Scenarios

### T32 Error Codes

#### T32_OK is zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(T32_OK).to_equal(0)
```

</details>

#### COM errors are negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(T32_ERR_COM_RECEIVE_FAIL).to_be_less_than(0)
expect(T32_ERR_COM_TRANSMIT_FAIL).to_be_less_than(0)
expect(T32_ERR_COM_RECEIVE_TIMEOUT).to_be_less_than(0)
```

</details>

#### general errors are positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(T32_ERR_FAIL).to_be_greater_than(0)
expect(T32_ERR_ATTACH_FAIL).to_be_greater_than(0)
```

</details>

### t32_error_message

#### maps OK to OK

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_error_message(T32_OK)).to_equal("OK")
```

</details>

#### maps COM receive fail

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_error_message(T32_ERR_COM_RECEIVE_FAIL)).to_contain("receive")
```

</details>

#### maps general failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_error_message(T32_ERR_FAIL)).to_contain("failure")
```

</details>

#### maps unknown codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_error_message(9999)).to_contain("Unknown")
```

</details>

### make_t32_error

#### creates error with code and message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = make_t32_error(T32_ERR_NOMEMORY)
expect(err.code).to_equal(T32_ERR_NOMEMORY)
expect(err.message).to_contain("memory")
```

</details>

### T32 Constants

#### state constants are distinct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(T32_STATE_DOWN != T32_STATE_HALTED).to_equal(true)
expect(T32_STATE_HALTED != T32_STATE_RUNNING).to_equal(true)
```

</details>

#### device type ICD is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(T32_DEV_ICD).to_equal(1)
```

</details>

#### register object sizes are correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(T32_REG_OBJ_R32).to_equal(32)
expect(T32_REG_OBJ_R64).to_equal(64)
```

</details>

#### group names are non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(T32_GROUP_CORE).to_equal("core")
expect(T32_GROUP_EXECUTE).to_equal("execute")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/debug/remote/t32_ffi/t32_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Error Codes
- t32_error_message
- make_t32_error
- T32 Constants

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
