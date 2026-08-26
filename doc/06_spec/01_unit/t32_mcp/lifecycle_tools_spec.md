# Lifecycle Tools Specification

> <details>

<!-- sdn-diagram:id=lifecycle_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lifecycle_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lifecycle_tools_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lifecycle_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lifecycle Tools Specification

## Scenarios

### t32_arch_to_binary

#### maps arm to t32marm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("arm")).to_equal("t32marm")
```

</details>

#### maps ARM (uppercase) to t32marm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("ARM")).to_equal("t32marm")
```

</details>

#### maps arm32 to t32marm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("arm32")).to_equal("t32marm")
```

</details>

#### maps cortex-m to t32marm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("cortex-m")).to_equal("t32marm")
```

</details>

#### maps cortex-a to t32marm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("cortex-a")).to_equal("t32marm")
```

</details>

#### maps empty string to default t32marm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("")).to_equal("t32marm")
```

</details>

#### maps arm64 to t32marm64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("arm64")).to_equal("t32marm64")
```

</details>

#### maps aarch64 to t32marm64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("aarch64")).to_equal("t32marm64")
```

</details>

#### maps ARM64 (uppercase) to t32marm64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("ARM64")).to_equal("t32marm64")
```

</details>

#### maps tricore to t32mtc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("tricore")).to_equal("t32mtc")
```

</details>

#### maps tc3xx to t32mtc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("tc3xx")).to_equal("t32mtc")
```

</details>

#### maps tc to t32mtc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("tc")).to_equal("t32mtc")
```

</details>

#### maps ppc to t32mppc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("ppc")).to_equal("t32mppc")
```

</details>

#### maps powerpc to t32mppc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("powerpc")).to_equal("t32mppc")
```

</details>

#### maps riscv to t32mriscv

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("riscv")).to_equal("t32mriscv")
```

</details>

#### maps risc-v to t32mriscv

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("risc-v")).to_equal("t32mriscv")
```

</details>

#### maps x86 to t32mx86

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("x86")).to_equal("t32mx86")
```

</details>

#### maps x86_64 to t32mx86

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("x86_64")).to_equal("t32mx86")
```

</details>

#### maps unknown arch to default t32marm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arch_to_binary("mips")).to_equal("t32marm")
```

</details>

### t32_find_install_dir

#### returns configured or standard install dir when present

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = find_install_dir()
val configured = env_get("T32MEM")
if configured != "":
    expect(dir).to_equal(configured)
elif file_exists("/opt/t32"):
    expect(dir).to_equal("/opt/t32")
else:
    expect(dir).to_equal("")
```

</details>

#### returns a stable result across repeated lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = find_install_dir()
expect(find_install_dir()).to_equal(dir)
```

</details>

### t32_check_xvfb

#### matches xvfb-run availability on the current host

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = check_xvfb()
val (_stdout, _stderr, rc) = process_run("/bin/sh", ["-c", "which xvfb-run 2>/dev/null"])
if rc == 0:
    expect(result).to_equal(true)
else:
    expect(result).to_equal(false)
```

</details>

### t32_ping_port

#### returns false when no service is listening on an unused port

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Port 19999 should not have a T32 instance running
val result = ping_port("t32rem64", 19999)
expect(result).to_equal(false)
```

</details>

#### returns false for an invalid backend on a closed port

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ping_port("t32rem64", 65000)
expect(result).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/t32_mcp/lifecycle_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- t32_arch_to_binary
- t32_find_install_dir
- t32_check_xvfb
- t32_ping_port

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
