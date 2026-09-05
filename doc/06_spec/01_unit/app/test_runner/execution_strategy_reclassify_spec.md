# Execution Strategy Reclassify Specification

> <details>

<!-- sdn-diagram:id=execution_strategy_reclassify_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=execution_strategy_reclassify_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

execution_strategy_reclassify_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=execution_strategy_reclassify_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Execution Strategy Reclassify Specification

## Scenarios

### Test file categorization

#### categorizes qemu test files

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_categorize("test/unit/qemu/riscv32_spec.spl")).to_equal("qemu")
```

</details>

#### categorizes emulator test files as qemu

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_categorize("test/unit/emulator/test_spec.spl")).to_equal("qemu")
```

</details>

#### categorizes baremetal test files

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_categorize("test/unit/baremetal/hello_spec.spl")).to_equal("baremetal")
```

</details>

#### categorizes kernel test files as baremetal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_categorize("test/unit/kernel/test_spec.spl")).to_equal("baremetal")
```

</details>

#### categorizes system test files

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_categorize("test/system/integration_spec.spl")).to_equal("system")
```

</details>

#### categorizes shared cross-platform test files

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_categorize("test/shared/core/primitives_spec.spl")).to_equal("shared")
```

</details>

#### categorizes unit test files

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mock_categorize("test/unit/parser/basic_spec.spl")).to_equal("unit")
```

</details>

### QEMU uses process mode with 120s timeout

#### selects process mode for qemu

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (mode, profile, timeout) = mock_strategy_select("test/unit/qemu/test_spec.spl")
expect(mode).to_equal("process")
expect(profile).to_equal("standard")
expect(timeout).to_equal(120)
```

</details>

### Baremetal uses process mode with 120s timeout

#### selects process mode for baremetal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (mode, profile, timeout) = mock_strategy_select("test/unit/baremetal/test_spec.spl")
expect(mode).to_equal("process")
expect(profile).to_equal("standard")
expect(timeout).to_equal(120)
```

</details>

### System tests use standard profile with 300s timeout

#### selects safe mode for system tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (mode, profile, timeout) = mock_strategy_select("test/system/daemon_spec.spl")
expect(mode).to_equal("safe")
expect(profile).to_equal("standard")
expect(timeout).to_equal(300)
```

</details>

### Unit tests use native mode with 60s timeout

#### selects native mode for unit tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (mode, profile, timeout) = mock_strategy_select("test/unit/parser/basic_spec.spl")
expect(mode).to_equal("native")
expect(profile).to_equal("fast")
expect(timeout).to_equal(60)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner/execution_strategy_reclassify_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Test file categorization
- QEMU uses process mode with 120s timeout
- Baremetal uses process mode with 120s timeout
- System tests use standard profile with 300s timeout
- Unit tests use native mode with 60s timeout

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
