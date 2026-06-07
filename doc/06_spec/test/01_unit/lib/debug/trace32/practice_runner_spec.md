# Practice Runner Specification

> <details>

<!-- sdn-diagram:id=practice_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=practice_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

practice_runner_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=practice_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Practice Runner Specification

## Scenarios

### T32 Practice Runner

#### formats DO command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "scripts/startup.cmm"
val cmd = "DO {script}"
expect(cmd).to_equal("DO scripts/startup.cmm")
```

</details>

#### formats DO with arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "scripts/flash.cmm"
val args = ["0x08000000", "firmware.elf"]
val args_str = args.join(" ")
val cmd = "DO {script} {args_str}"
expect(cmd).to_equal("DO scripts/flash.cmm 0x08000000 firmware.elf")
```

</details>

#### formats PRACTICE.STATE query

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "PRACTICE.STATE()"
expect(cmd).to_equal("PRACTICE.STATE()")
```

</details>

#### formats EVAL expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expr = "Register(PC)"
val cmd = "EVAL {expr}"
expect(cmd).to_equal("EVAL Register(PC)")
```

</details>

#### formats InterCom execute

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "ARM_A53_0"
val inner_cmd = "SYStem.Mode.Prepare"
val cmd = "InterCom.execute {target} {inner_cmd}"
expect(cmd).to_equal("InterCom.execute ARM_A53_0 SYStem.Mode.Prepare")
```

</details>

#### formats WinPrint command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val window = "Break.List"
val cmd = "WinPrint.{window}"
expect(cmd).to_equal("WinPrint.Break.List")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/debug/trace32/practice_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Practice Runner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
