# Smoke Rustc Specification

> _Env-gated checks for a working Rust cross-toolchain targeting x86_64-unknown-simpleos._

<!-- sdn-diagram:id=smoke_rustc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smoke_rustc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smoke_rustc_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smoke_rustc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smoke Rustc Specification

## Scenarios

### SimpleOS Rust cross-compile smoke
_Env-gated checks for a working Rust cross-toolchain targeting x86_64-unknown-simpleos._

#### target JSON exists at src/os/toolchain/rust/x86_64-unknown-simpleos.json

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs.exists(TARGET_JSON).to_equal(true)
```

</details>

#### rustc --print target-list contains simpleos when using forked rustc

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rs = rust_src()
if rs == "":
    return "skip: RUST_SRC not set — forked rustc not configured"
val rustc = "{rs}/bin/rustc"
val (out, err, code) = process.run(rustc, ["--print", "target-list"])
code.to_equal(0)
out.contains("simpleos").to_equal(true)
```

</details>

#### cargo +nightly build --target x86_64-unknown-simpleos exits 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if rust_gate() == false:
    return "skip: no RUST_SRC and no system nightly rustc"
val dry = rt_env_get("RUST_BUILD_DRY_RUN")
if dry == "1":
    return "skip: RUST_BUILD_DRY_RUN=1"
val sysroot = rt_env_get("SIMPLEOS_SYSROOT")
if sysroot == nil:
    return "skip: SIMPLEOS_SYSROOT not set"
if sysroot == "":
    return "skip: SIMPLEOS_SYSROOT not set"
val (out, err, code) = process.run("cargo", [
    "+nightly",
    "build",
    "--release",
    "--target",
    "../../src/os/toolchain/rust/x86_64-unknown-simpleos.json",
    "-Z",
    "build-std=core,alloc,compiler_builtins",
], HELLO_RS_DIR)
code.to_equal(0)
```

</details>

#### output binary exists after build

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if rust_gate() == false:
    return "skip: no RUST_SRC and no system nightly rustc"
val dry = rt_env_get("RUST_BUILD_DRY_RUN")
if dry == "1":
    return "skip: RUST_BUILD_DRY_RUN=1"
val sysroot = rt_env_get("SIMPLEOS_SYSROOT")
if sysroot == nil:
    return "skip: SIMPLEOS_SYSROOT not set"
if sysroot == "":
    return "skip: SIMPLEOS_SYSROOT not set"
fs.exists(HELLO_RS_OUT).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/rust/smoke_rustc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Rust cross-compile smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
