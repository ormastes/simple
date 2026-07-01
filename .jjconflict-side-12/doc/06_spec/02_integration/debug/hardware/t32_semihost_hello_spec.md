# T32 Semihost Hello Specification

> <details>

<!-- sdn-diagram:id=t32_semihost_hello_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_semihost_hello_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_semihost_hello_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_semihost_hello_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Semihost Hello Specification

## Scenarios

### T32 semihost hello-world runner

#### ships the runner script

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("scripts/t32_semihost_hello.shs")).to_equal(true)
```

</details>

#### reuses the shared STM semihost smoke fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists("test/fixtures/baremetal/stm_semihost_smoke.s")).to_equal(true)
expect(rt_file_exists("test/fixtures/baremetal/stm_semihost_smoke.ld")).to_equal(true)
```

</details>

#### runner help documents board and build-only options

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = shell("scripts/t32_semihost_hello.shs --help 2>&1")
expect(output).to_contain("--board")
expect(output).to_contain("--build-only")
expect(output).to_contain("stm32wb")
expect(output).to_contain("stm32h7")
```

</details>

#### build-only mode emits the STM smoke ELF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = shell("scripts/t32_semihost_hello.shs --build-only 2>&1")
expect(output).to_contain("built ELF:")
expect(output).to_contain("stm_semihost_smoke")
```

</details>

#### documents the expected semihost marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = shell("sed -n '1,200p' scripts/t32_semihost_hello.shs")
expect(output).to_contain("simple-stm-smoke")
expect(output).to_contain("WinPrint.AREA MCP_OUT")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/debug/hardware/t32_semihost_hello_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 semihost hello-world runner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
