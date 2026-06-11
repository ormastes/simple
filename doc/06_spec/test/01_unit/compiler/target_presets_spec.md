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
| 23 | 23 | 0 | 0 |

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

#### returns a list of 11 preset names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = spec_all_names()
expect(names.len()).to_equal(11)
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

#### baremetal preset family mapping

#### restricts to nogc_async_mut_noalloc and common

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m4()
# Baremetal presets (no_std + no_gc) should only allow these two families
val families = p.allowed_families
expect(families.len()).to_equal(2)
expect(families[0]).to_equal("nogc_async_mut_noalloc")
expect(families[1]).to_equal("common")
```

</details>

#### sets gc_off to true for baremetal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m4()
expect(p.no_gc).to_equal(true)
```

</details>

#### disallows allocation for baremetal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_cortex_m4()
expect(p.heap_size).to_equal(0)
```

</details>

#### hosted preset family mapping

#### allows all families (empty restriction)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_linux_x86_64()
val families = p.allowed_families
expect(families.len()).to_equal(0)
```

</details>

#### does not set gc_off for hosted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_linux_x86_64()
expect(p.no_gc).to_equal(false)
```

</details>

#### embedded_with_heap preset family mapping

#### allows nogc families plus common but not gc

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = make_wasm32()
val families = p.allowed_families
expect(families.len()).to_equal(4)
expect(families[0]).to_equal("nogc_async_mut_noalloc")
expect(families[1]).to_equal("nogc_sync_mut")
expect(families[2]).to_equal("nogc_async_mut")
expect(families[3]).to_equal("common")
```

</details>

#### is_family_allowed helper

#### allows any family when restriction is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families: [text] = []
expect(check_family_allowed(families, "gc_async_mut")).to_equal(true)
expect(check_family_allowed(families, "nogc_sync_mut")).to_equal(true)
```

</details>

#### blocks non-listed families when restriction is active

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val families = ["nogc_async_mut_noalloc", "common"]
expect(check_family_allowed(families, "nogc_async_mut_noalloc")).to_equal(true)
expect(check_family_allowed(families, "common")).to_equal(true)
expect(check_family_allowed(families, "nogc_sync_mut")).to_equal(false)
expect(check_family_allowed(families, "gc_async_mut")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/target_presets_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TargetPreset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
