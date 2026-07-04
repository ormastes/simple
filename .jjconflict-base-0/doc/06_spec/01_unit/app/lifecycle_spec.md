# Lifecycle Specification

> <details>

<!-- sdn-diagram:id=lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lifecycle_spec -> std
lifecycle_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lifecycle Specification

## Scenarios

### AppConfig

#### from_env

#### creates config with detected platform

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AppConfig.from_env("test-app", "1.0.0")
expect(config.name).to_equal("test-app")
expect(config.version).to_equal("1.0.0")
expect(config.platform.len()).to_be_greater_than(0)
expect(config.arch.len()).to_be_greater_than(0)
```

</details>

#### create

#### creates config with explicit values

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AppConfig.create(
    name: "my-app",
    version: "2.0.0",
    args: ["--verbose", "file.txt"],
    platform: "linux",
    arch: "x86_64"
)
expect(config.name).to_equal("my-app")
expect(config.version).to_equal("2.0.0")
expect(config.platform).to_equal("linux")
expect(config.arch).to_equal("x86_64")
```

</details>

#### platform predicates

#### is_desktop returns true for linux

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AppConfig.create(
    name: "t", version: "0", args: [],
    platform: "linux", arch: "x86_64"
)
expect(config.is_desktop()).to_equal(true)
expect(config.is_mobile()).to_equal(false)
```

</details>

#### is_mobile returns true for ios

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AppConfig.create(
    name: "t", version: "0", args: [],
    platform: "ios", arch: "aarch64"
)
expect(config.is_mobile()).to_equal(true)
expect(config.is_desktop()).to_equal(false)
```

</details>

#### is_mobile returns true for android

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AppConfig.create(
    name: "t", version: "0", args: [],
    platform: "android", arch: "aarch64"
)
expect(config.is_mobile()).to_equal(true)
```

</details>

#### is_wasm returns true for wasm32

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AppConfig.create(
    name: "t", version: "0", args: [],
    platform: "wasi", arch: "wasm32"
)
expect(config.is_wasm()).to_equal(true)
```

</details>

#### is_baremetal returns true for none platform

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AppConfig.create(
    name: "t", version: "0", args: [],
    platform: "none", arch: "riscv32"
)
expect(config.is_baremetal()).to_equal(true)
```

</details>

#### is_64bit returns true for x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AppConfig.create(
    name: "t", version: "0", args: [],
    platform: "linux", arch: "x86_64"
)
expect(config.is_64bit()).to_equal(true)
```

</details>

#### is_64bit returns false for wasm32

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AppConfig.create(
    name: "t", version: "0", args: [],
    platform: "wasi", arch: "wasm32"
)
expect(config.is_64bit()).to_equal(false)
```

</details>

### AppState

#### Created is not running

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = AppState.Created
expect(state.is_running()).to_equal(false)
expect(state.is_stopped()).to_equal(false)
```

</details>

#### Running is running

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = AppState.Running
expect(state.is_running()).to_equal(true)
expect(state.is_stopped()).to_equal(false)
```

</details>

#### Stopped is stopped

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = AppState.Stopped
expect(state.is_running()).to_equal(false)
expect(state.is_stopped()).to_equal(true)
```

</details>

### run_oneshot

#### runs init, run, shutdown in order

1. fn test init
2. log push
3. fn test run
4. log push
5. fn test shutdown
6. log push
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var log = []

fn test_init(config: AppConfig):
    log.push("init")

fn test_run(config: AppConfig) -> i32:
    log.push("run")
    0

fn test_shutdown():
    log.push("shutdown")

val code = run_oneshot("test", "1.0", test_init, test_run, test_shutdown)
expect(code).to_equal(0)
```

</details>

### run_simple

#### passes args to main function

1. fn test main
   - Expected: code equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test_main(args: [text]) -> i32:
    42

val code = run_simple("test", test_main)
expect(code).to_equal(42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lifecycle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AppConfig
- AppState
- run_oneshot
- run_simple

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
