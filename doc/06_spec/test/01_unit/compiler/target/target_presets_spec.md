# Target Presets Specification

> <details>

<!-- sdn-diagram:id=target_presets_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=target_presets_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

target_presets_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=target_presets_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Target Presets Specification

## Scenarios

### TargetPreset

#### cortex-m4 preset

#### has the correct name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m4()
expect(p.name).to_equal("cortex-m4")
```

</details>

#### has the correct arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m4()
expect(p.arch).to_equal("thumbv7em")
```

</details>

#### is bare-metal (no_std and no_gc)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m4()
expect(spec_is_baremetal(p)).to_equal(true)
```

</details>

#### has pointer_width of 32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m4()
expect(p.pointer_width).to_equal(32)
```

</details>

#### has float_support enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m4()
expect(p.float_support).to_equal(true)
```

</details>

#### riscv32-baremetal preset

#### has os set to none

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_riscv32_baremetal()
expect(p.os).to_equal("none")
```

</details>

#### wasm32 preset

#### has arch set to wasm32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_wasm32()
expect(p.arch).to_equal("wasm32")
```

</details>

#### linux-x86_64 preset

#### is not bare-metal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_linux_x86_64()
expect(spec_is_baremetal(p)).to_equal(false)
```

</details>

#### preset_by_name lookup

#### returns cortex-m4 when asked by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_by_name("cortex-m4")
expect(p.name).to_equal("cortex-m4")
```

</details>

#### returns wasm32 when asked by name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_by_name("wasm32")
expect(p.arch).to_equal("wasm32")
```

</details>

#### returns unknown-default preset for unknown name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_by_name("nonexistent-target")
expect(p.arch).to_equal("unknown")
```

</details>

#### preset_triple

#### formats triple as arch-os-abi

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m4()
val triple = spec_triple(p)
expect(triple).to_equal("thumbv7em-none-eabihf")
```

</details>

#### preset_all_names

#### returns a list of 8 preset names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = spec_all_names()
expect(names.len()).to_equal(8)
```

</details>

#### cortex-m0 preset

#### has no float_support

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m0()
expect(p.float_support).to_equal(false)
```

</details>

#### macos-arm64 preset

#### has pointer_width of 64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_macos_arm64()
expect(p.pointer_width).to_equal(64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/target/target_presets_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TargetPreset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
