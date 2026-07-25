# Config Specification

> 1. fn run

<!-- sdn-diagram:id=config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

config_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Config Specification

## Scenarios

### parse_leak_check_args

#### parses source file as positional argument

1. fn run
   - Expected: cfg.source_file equals `test.spl`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val cfg = parse_leak_check_args(["test.spl"])
    expect(cfg.source_file).to_equal("test.spl")
run()
```

</details>

#### parses --verbose flag

1. fn run
   - Expected: cfg.verbose is true
   - Expected: cfg.source_file equals `test.spl`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val cfg = parse_leak_check_args(["--verbose", "test.spl"])
    expect(cfg.verbose).to_equal(true)
    expect(cfg.source_file).to_equal("test.spl")
run()
```

</details>

#### parses --mode=external

1. fn run
   - Expected: cfg.source_file equals `test.spl`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val cfg = parse_leak_check_args(["--mode=external", "test.spl"])
    expect(cfg.source_file).to_equal("test.spl")
run()
```

</details>

#### parses --timeout=20

1. fn run
   - Expected: cfg.timeout_seconds equals `20`
   - Expected: cfg.source_file equals `test.spl`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val cfg = parse_leak_check_args(["--timeout=20", "test.spl"])
    expect(cfg.timeout_seconds).to_equal(20)
    expect(cfg.source_file).to_equal("test.spl")
run()
```

</details>

#### uses default timeout of 10

1. fn run
   - Expected: cfg.timeout_seconds equals `10`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val cfg = parse_leak_check_args(["test.spl"])
    expect(cfg.timeout_seconds).to_equal(10)
run()
```

</details>

#### parses --help and returns empty source

1. fn run
   - Expected: cfg.source_file equals ``
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val cfg = parse_leak_check_args(["--help"])
    expect(cfg.source_file).to_equal("")
run()
```

</details>

#### parses multiple flags together

1. fn run
   - Expected: cfg.verbose is true
   - Expected: cfg.timeout_seconds equals `15`
   - Expected: cfg.gc_leak_window equals `5`
   - Expected: cfg.source_file equals `my_file.spl`
2. run


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run():
    val cfg = parse_leak_check_args(["--verbose", "--timeout=15", "--gc-window=5", "my_file.spl"])
    expect(cfg.verbose).to_equal(true)
    expect(cfg.timeout_seconds).to_equal(15)
    expect(cfg.gc_leak_window).to_equal(5)
    expect(cfg.source_file).to_equal("my_file.spl")
run()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/leak_check/config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- parse_leak_check_args

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
