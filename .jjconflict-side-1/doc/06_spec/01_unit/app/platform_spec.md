# Platform Specification

> <details>

<!-- sdn-diagram:id=platform_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=platform_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

platform_spec -> std
platform_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=platform_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Platform Specification

## Scenarios

### AppConfig platform detection

#### from_env detects current platform

#### detects a known platform

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AppConfig.from_env("test", "1.0")
val p = config.platform
# Must be one of the known platforms
val known = p == "linux" or p == "macos" or p == "windows" or p == "freebsd"
expect(known).to_equal(true)
```

</details>

#### detects a known architecture

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = AppConfig.from_env("test", "1.0")
val a = config.arch
val known = a == "x86_64" or a == "aarch64" or a == "riscv64" or a == "i686"
expect(known).to_equal(true)
```

</details>

#### desktop platforms

#### linux is desktop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "linux", arch: "x86_64")
expect(c.is_desktop()).to_equal(true)
```

</details>

#### macos is desktop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "macos", arch: "aarch64")
expect(c.is_desktop()).to_equal(true)
```

</details>

#### windows is desktop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "windows", arch: "x86_64")
expect(c.is_desktop()).to_equal(true)
```

</details>

#### freebsd is desktop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "freebsd", arch: "x86_64")
expect(c.is_desktop()).to_equal(true)
```

</details>

#### mobile platforms

#### ios is mobile

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "ios", arch: "aarch64")
expect(c.is_mobile()).to_equal(true)
expect(c.is_desktop()).to_equal(false)
```

</details>

#### android is mobile

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "android", arch: "aarch64")
expect(c.is_mobile()).to_equal(true)
expect(c.is_desktop()).to_equal(false)
```

</details>

#### wasm platforms

#### wasm32 is wasm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "wasi", arch: "wasm32")
expect(c.is_wasm()).to_equal(true)
expect(c.is_desktop()).to_equal(false)
```

</details>

#### wasm64 is wasm

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "wasi", arch: "wasm64")
expect(c.is_wasm()).to_equal(true)
```

</details>

#### bare-metal

#### none platform is baremetal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "none", arch: "riscv32")
expect(c.is_baremetal()).to_equal(true)
expect(c.is_desktop()).to_equal(false)
```

</details>

#### bitness

#### x86_64 is 64-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "linux", arch: "x86_64")
expect(c.is_64bit()).to_equal(true)
```

</details>

#### aarch64 is 64-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "ios", arch: "aarch64")
expect(c.is_64bit()).to_equal(true)
```

</details>

#### riscv64 is 64-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "linux", arch: "riscv64")
expect(c.is_64bit()).to_equal(true)
```

</details>

#### wasm32 is not 64-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "wasi", arch: "wasm32")
expect(c.is_64bit()).to_equal(false)
```

</details>

#### riscv32 is not 64-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "none", arch: "riscv32")
expect(c.is_64bit()).to_equal(false)
```

</details>

#### platform exclusivity

#### desktop is not mobile, wasm, or baremetal

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "linux", arch: "x86_64")
expect(c.is_desktop()).to_equal(true)
expect(c.is_mobile()).to_equal(false)
expect(c.is_wasm()).to_equal(false)
expect(c.is_baremetal()).to_equal(false)
```

</details>

#### mobile is not desktop, wasm, or baremetal

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = AppConfig.create(name: "t", version: "0", args: [], platform: "android", arch: "aarch64")
expect(c.is_mobile()).to_equal(true)
expect(c.is_desktop()).to_equal(false)
expect(c.is_wasm()).to_equal(false)
expect(c.is_baremetal()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/platform_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- AppConfig platform detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
