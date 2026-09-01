# Lifecycle Specification

> Tests covering AppConfig, AppState, run_oneshot, run_simple.

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

- creates config with detected platform
   - Expected: config.name equals `test-app`
   - Expected: config.version equals `1.0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates config with detected platform")
val config = AppConfig.from_env("test-app", "1.0.0")
expect(config.name).to_equal("test-app")
expect(config.version).to_equal("1.0.0")
expect(config.platform.len()).to_be_greater_than(0)
expect(config.arch.len()).to_be_greater_than(0)
```

</details>

#### create

#### creates config with explicit values

- creates config with explicit values
   - Expected: config.name equals `my-app`
   - Expected: config.version equals `2.0.0`
   - Expected: config.platform equals `linux`
   - Expected: config.arch equals `x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates config with explicit values")
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

- is_desktop returns true for linux
   - Expected: config.is_desktop() is true
   - Expected: config.is_mobile() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_desktop returns true for linux")
val config = AppConfig.create(
    name: "t", version: "0", args: [],
    platform: "linux", arch: "x86_64"
)
expect(config.is_desktop()).to_equal(true)
expect(config.is_mobile()).to_equal(false)
```

</details>

#### is_mobile returns true for ios

- is_mobile returns true for ios
   - Expected: config.is_mobile() is true
   - Expected: config.is_desktop() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_mobile returns true for ios")
val config = AppConfig.create(
    name: "t", version: "0", args: [],
    platform: "ios", arch: "aarch64"
)
expect(config.is_mobile()).to_equal(true)
expect(config.is_desktop()).to_equal(false)
```

</details>

#### is_mobile returns true for android

- is_mobile returns true for android
   - Expected: config.is_mobile() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_mobile returns true for android")
val config = AppConfig.create(
    name: "t", version: "0", args: [],
    platform: "android", arch: "aarch64"
)
expect(config.is_mobile()).to_equal(true)
```

</details>

#### is_wasm returns true for wasm32

- is_wasm returns true for wasm32
   - Expected: config.is_wasm() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_wasm returns true for wasm32")
val config = AppConfig.create(
    name: "t", version: "0", args: [],
    platform: "wasi", arch: "wasm32"
)
expect(config.is_wasm()).to_equal(true)
```

</details>

#### is_baremetal returns true for none platform

- is_baremetal returns true for none platform
   - Expected: config.is_baremetal() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_baremetal returns true for none platform")
val config = AppConfig.create(
    name: "t", version: "0", args: [],
    platform: "none", arch: "riscv32"
)
expect(config.is_baremetal()).to_equal(true)
```

</details>

#### is_64bit returns true for x86_64

- is_64bit returns true for x86_64
   - Expected: config.is_64bit() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_64bit returns true for x86_64")
val config = AppConfig.create(
    name: "t", version: "0", args: [],
    platform: "linux", arch: "x86_64"
)
expect(config.is_64bit()).to_equal(true)
```

</details>

#### is_64bit returns false for wasm32

- is_64bit returns false for wasm32
   - Expected: config.is_64bit() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_64bit returns false for wasm32")
val config = AppConfig.create(
    name: "t", version: "0", args: [],
    platform: "wasi", arch: "wasm32"
)
expect(config.is_64bit()).to_equal(false)
```

</details>

### AppState

#### Created is not running

- Created is not running
   - Expected: state.is_running() is false
   - Expected: state.is_stopped() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Created is not running")
val state = AppState.Created
expect(state.is_running()).to_equal(false)
expect(state.is_stopped()).to_equal(false)
```

</details>

#### Running is running

- Running is running
   - Expected: state.is_running() is true
   - Expected: state.is_stopped() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Running is running")
val state = AppState.Running
expect(state.is_running()).to_equal(true)
expect(state.is_stopped()).to_equal(false)
```

</details>

#### Stopped is stopped

- Stopped is stopped
   - Expected: state.is_running() is false
   - Expected: state.is_stopped() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Stopped is stopped")
val state = AppState.Stopped
expect(state.is_running()).to_equal(false)
expect(state.is_stopped()).to_equal(true)
```

</details>

### run_oneshot

#### runs init, run, shutdown in order

- runs init, run, shutdown in order
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs init, run, shutdown in order")
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

- passes args to main function
   - Expected: code equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes args to main function")
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
| Source | `test/unit/app/lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AppConfig, AppState, run_oneshot, run_simple.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `791067936b620379594eaed0cd2ae5e90a877f83eb7268238d5e9b3ea63e498a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `791067936b620379594eaed0cd2ae5e90a877f83eb7268238d5e9b3ea63e498a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `791067936b620379594eaed0cd2ae5e90a877f83eb7268238d5e9b3ea63e498a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/lifecycle_spec.spl
mirror: doc/06_spec/unit/app/lifecycle_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lifecycle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/lifecycle_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates config with detected platform' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lifecycle_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates config with explicit values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lifecycle_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_desktop returns true for linux' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
