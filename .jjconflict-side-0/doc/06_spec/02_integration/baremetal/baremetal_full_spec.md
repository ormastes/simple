# Baremetal Full Specification

> <details>

<!-- sdn-diagram:id=baremetal_full_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=baremetal_full_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

baremetal_full_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=baremetal_full_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Baremetal Full Specification

## Scenarios

### Baremetal Integration Smoke

#### simple os CLI surface

#### prints top-level baremetal help

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "bin/simple os --help"
val stdout = shell_stdout(cmd)
expect(shell_exit_code(cmd)).to_equal(0)
expect(stdout.contains("Build the OS kernel")).to_equal(true)
expect(stdout.contains("Build and run in QEMU")).to_equal(true)
expect(stdout.contains("Build and run boot smoke test")).to_equal(true)
expect(stdout.contains("List supported architectures")).to_equal(true)
```

</details>

#### lists the six supported baremetal architectures

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "bin/simple os targets"
val stdout = shell_stdout(cmd)
expect(shell_exit_code(cmd)).to_equal(0)
expect(stdout.contains("x86_64  ->  x86_64-unknown-none  (qemu-system-x86_64)")).to_equal(true)
expect(stdout.contains("x86_32  ->  i686-unknown-none  (qemu-system-i386)")).to_equal(true)
expect(stdout.contains("riscv64  ->  riscv64-unknown-none  (qemu-system-riscv64)")).to_equal(true)
expect(stdout.contains("riscv32  ->  riscv32-unknown-none  (qemu-system-riscv32)")).to_equal(true)
expect(stdout.contains("arm64  ->  aarch64-unknown-none  (qemu-system-aarch64)")).to_equal(true)
expect(stdout.contains("arm32  ->  armv7-unknown-none-eabihf  (qemu-system-arm)")).to_equal(true)
expect(stdout.contains("Default: x86_64")).to_equal(true)
```

</details>

#### argument validation

#### rejects unknown architecture for build before a compile starts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "bin/simple os build --arch=bogus"
val stderr = shell_stderr(cmd)
expect(shell_exit_code(cmd)).to_equal(1)
expect(stderr.contains("unknown architecture 'bogus'")).to_equal(true)
expect(stderr.contains("Run 'simple os targets' for supported architectures.")).to_equal(true)
```

</details>

#### rejects unknown architecture for run before a qemu launch starts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "bin/simple os run --arch=bogus"
val stderr = shell_stderr(cmd)
expect(shell_exit_code(cmd)).to_equal(1)
expect(stderr.contains("unknown architecture 'bogus'")).to_equal(true)
expect(stderr.contains("Run 'simple os targets' for supported architectures.")).to_equal(true)
```

</details>

#### checked-in baremetal assets

#### has boot entries and linker scripts for every reported architecture

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(all_baremetal_assets_exist()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/02_integration/baremetal/baremetal_full_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Baremetal Integration Smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
