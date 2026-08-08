# Replay Cli Dispatch Specification

> <details>

<!-- sdn-diagram:id=replay_cli_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_cli_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_cli_dispatch_spec -> std
replay_cli_dispatch_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_cli_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Cli Dispatch Specification

## Scenarios

### qemu subcommand parse_flag

#### parse_flag extracts --arch value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ["--arch", "x86_64", "--kernel", "boot.elf"]
val v = parse_flag(a, "--arch")
expect(v).to_equal("x86_64")
```

</details>

#### parse_flag extracts --kernel value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ["--arch", "riscv32", "--kernel", "boot.elf", "--trace", "out.srrq"]
val v = parse_flag(a, "--kernel")
expect(v).to_equal("boot.elf")
```

</details>

#### parse_flag extracts --trace value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ["--arch", "x86_64", "--kernel", "boot.elf", "--trace", "recording.srrq"]
val v = parse_flag(a, "--trace")
expect(v).to_equal("recording.srrq")
```

</details>

#### parse_flag extracts --gdb-port value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ["--kernel", "boot.elf", "--trace", "rec.srrq", "--gdb-port", "5555"]
val v = parse_flag(a, "--gdb-port")
expect(v).to_equal("5555")
```

</details>

#### parse_flag returns empty text for missing flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ["--arch", "x86_64"]
val v = parse_flag(a, "--kernel")
expect(v).to_equal("")
```

</details>

#### parse_flag returns empty for unrelated args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ["--unrelated", "value"]
val v = parse_flag(a, "--arch")
expect(v).to_equal("")
```

</details>

#### parse_flag extracts --qmp socket path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ["save", "snap1", "--qmp", "/tmp/qemu-qmp.sock"]
val v = parse_flag(a, "--qmp")
expect(v).to_equal("/tmp/qemu-qmp.sock")
```

</details>

#### parse_flag extracts --machine value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = ["--arch", "aarch64", "--kernel", "k.elf", "--machine", "virt"]
val v = parse_flag(a, "--machine")
expect(v).to_equal("virt")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_cli_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- qemu subcommand parse_flag

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
