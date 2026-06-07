# Test Env Gate Specification

> 1. rt env remove

<!-- sdn-diagram:id=test_env_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_env_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_env_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_env_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Env Gate Specification

## Scenarios

### test_env_require

#### returns blocked: prefix when env var is not set

1. rt env remove
   - Expected: result equals `blocked:SIMPLE_TEST_PROBE_GATE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_remove("SIMPLE_TEST_PROBE_GATE")
val result = test_env_require("SIMPLE_TEST_PROBE_GATE")
expect(result).to_equal("blocked:SIMPLE_TEST_PROBE_GATE")
```

</details>

#### returns ready when env var is set to 1

1. rt env set
2. rt env remove
   - Expected: result equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_TEST_PROBE_GATE", "1")
val result = test_env_require("SIMPLE_TEST_PROBE_GATE")
rt_env_remove("SIMPLE_TEST_PROBE_GATE")
expect(result).to_equal("ready")
```

</details>

#### returns blocked when env var is set to 0

1. rt env set
2. rt env remove
   - Expected: result equals `blocked:SIMPLE_TEST_PROBE_GATE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_TEST_PROBE_GATE", "0")
val result = test_env_require("SIMPLE_TEST_PROBE_GATE")
rt_env_remove("SIMPLE_TEST_PROBE_GATE")
expect(result).to_equal("blocked:SIMPLE_TEST_PROBE_GATE")
```

</details>

#### blocked: prefix contains the env var name exactly

1. rt env remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_remove("SIMPLE_TEST_PROBE_GATE")
val result = test_env_require("SIMPLE_TEST_PROBE_GATE")
expect(result).to_contain("SIMPLE_TEST_PROBE_GATE")
```

</details>

#### blocked: result starts with blocked:

1. rt env remove


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_remove("SIMPLE_TEST_PROBE_GATE")
val result = test_env_require("SIMPLE_TEST_PROBE_GATE")
expect(result).to_start_with("blocked:")
```

</details>

### test_env_available

#### returns false when env var is absent

1. rt env remove
   - Expected: test_env_available("SIMPLE_TEST_PROBE_AVAIL") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_remove("SIMPLE_TEST_PROBE_AVAIL")
expect(test_env_available("SIMPLE_TEST_PROBE_AVAIL")).to_equal(false)
```

</details>

#### returns true when env var is set to 1

1. rt env set
2. rt env remove
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_TEST_PROBE_AVAIL", "1")
val result = test_env_available("SIMPLE_TEST_PROBE_AVAIL")
rt_env_remove("SIMPLE_TEST_PROBE_AVAIL")
expect(result).to_equal(true)
```

</details>

#### returns false when env var is set to empty string

1. rt env set
2. rt env remove
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_set("SIMPLE_TEST_PROBE_AVAIL", "")
val result = test_env_available("SIMPLE_TEST_PROBE_AVAIL")
rt_env_remove("SIMPLE_TEST_PROBE_AVAIL")
expect(result).to_equal(false)
```

</details>

### test_env_hardware_available

#### returns false when SIMPLE_HW_TEST is not set to 1

1. rt env remove
   - Expected: test_env_hardware_available() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_remove("SIMPLE_HW_TEST")
expect(test_env_hardware_available()).to_equal(false)
```

</details>

### test_env_qemu_available

#### returns false when SIMPLE_QEMU_TEST is not set to 1

1. rt env remove
   - Expected: test_env_qemu_available() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_remove("SIMPLE_QEMU_TEST")
expect(test_env_qemu_available()).to_equal(false)
```

</details>

### test_env_network_available

#### returns false when SIMPLE_NET_TEST is not set to 1

1. rt env remove
   - Expected: test_env_network_available() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rt_env_remove("SIMPLE_NET_TEST")
expect(test_env_network_available()).to_equal(false)
```

</details>

### test_env_gate_reason

#### contains the env var name in the reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_reason("SIMPLE_HW_TEST")
expect(reason).to_contain("SIMPLE_HW_TEST")
```

</details>

#### instructs the user to set the var to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_reason("SIMPLE_HW_TEST")
expect(reason).to_contain("=1")
```

</details>

#### uses the correct env name for hardware gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_reason("SIMPLE_HW_TEST")
expect(reason).to_contain("SIMPLE_HW_TEST")
```

</details>

#### uses the correct env name for qemu gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_reason("SIMPLE_QEMU_TEST")
expect(reason).to_contain("SIMPLE_QEMU_TEST")
```

</details>

#### uses the correct env name for network gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_reason("SIMPLE_NET_TEST")
expect(reason).to_contain("SIMPLE_NET_TEST")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/test_env_gate/test_env_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- test_env_require
- test_env_available
- test_env_hardware_available
- test_env_qemu_available
- test_env_network_available
- test_env_gate_reason

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
