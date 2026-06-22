# Reporter Specification

> 1. fn run

<!-- sdn-diagram:id=reporter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=reporter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

reporter_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=reporter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reporter Specification

## Scenarios

### format_bytes

#### formats small byte counts

1. fn run
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val r0 = format_bytes(0)
    expect(r0).to_contain("0")
    val r512 = format_bytes(512)
    expect(r512).to_contain("512")
run()
```

</details>

#### formats KB range

1. fn run
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val r1k = format_bytes(1024)
    expect(r1k).to_contain("KB")
    val r2k = format_bytes(2048)
    expect(r2k).to_contain("KB")
run()
```

</details>

#### formats MB range

1. fn run
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val r1m = format_bytes(1048576)
    expect(r1m).to_contain("MB")
    val r2m = format_bytes(2097152)
    expect(r2m).to_contain("MB")
run()
```

</details>

### report_console

#### shows no leaks verdict for clean result

1. fn run
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val result = empty_leak_check_result()
    val output = report_console(result)
    expect(output).to_contain("No leaks detected")
    expect(output).to_contain("VERDICT")
run()
```

</details>

#### shows mode in report

1. fn run
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val result = empty_leak_check_result()
    val output = report_console(result)
    expect(output).to_contain("Mode: internal")
run()
```

</details>

### escape_sdn

#### escapes backslashes

1. fn run
   - Expected: result equals `hello world`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val result = escape_sdn("hello world")
    expect(result).to_equal("hello world")
run()
```

</details>

#### leaves clean strings unchanged

1. fn run
   - Expected: result equals `hello world`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val result = escape_sdn("hello world")
    expect(result).to_equal("hello world")
run()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/leak_check/reporter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- format_bytes
- report_console
- escape_sdn

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
