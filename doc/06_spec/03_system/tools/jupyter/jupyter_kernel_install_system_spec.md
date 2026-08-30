# Jupyter Kernel Install System Specification

> <details>

<!-- sdn-diagram:id=jupyter_kernel_install_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jupyter_kernel_install_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jupyter_kernel_install_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jupyter_kernel_install_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jupyter Kernel Install System Specification

## Scenarios

### Jupyter Kernel Installation

<details>
<summary>Advanced: should have kernel.json</summary>

#### should have kernel.json _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("tools/jupyter/kernel.json")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should have kernel_wrapper.py</summary>

#### should have kernel_wrapper.py _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("tools/jupyter/kernel_wrapper.py")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should have install script</summary>

#### should have install script _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("tools/jupyter/install.shs")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should have valid kernel.json with Simple language</summary>

#### should have valid kernel.json with Simple language _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("tools/jupyter/kernel.json") ?? ""
expect(content).to_contain("Simple")
expect(content).to_contain("simple")
expect(content).to_contain(".spl")
```

</details>


</details>

<details>
<summary>Advanced: should have kernel main entry point</summary>

#### should have kernel main entry point _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("src/app/jupyter_kernel/main.spl")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should have kernel protocol module</summary>

#### should have kernel protocol module _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("src/app/jupyter_kernel/protocol.spl")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: should have kernel session module</summary>

#### should have kernel session module _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("src/app/jupyter_kernel/session.spl")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/jupyter/jupyter_kernel_install_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Jupyter Kernel Installation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 7 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
