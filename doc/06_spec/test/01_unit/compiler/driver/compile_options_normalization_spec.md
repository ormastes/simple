# Compile Options Normalization Specification

> <details>

<!-- sdn-diagram:id=compile_options_normalization_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compile_options_normalization_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compile_options_normalization_spec -> std
compile_options_normalization_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compile_options_normalization_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compile Options Normalization Specification

## Scenarios

### compile option normalization

#### keeps debug defaults at opt level zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = normalized_options(false, false, "dev", nil)
expect(options.release).to_equal(false)
expect(options.optimize).to_equal(false)
expect(options.opt_level).to_equal(0)
expect(compileoptions_effective_mir_opt_level(options)).to_equal(0)
```

</details>

#### normalizes release-only requests to the standard mir level

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = normalized_options(true, false, "prod", nil)
expect(options.release).to_equal(true)
expect(options.optimize).to_equal(true)
expect(options.opt_level).to_equal(2)
expect(compileoptions_effective_mir_opt_level(options)).to_equal(2)
```

</details>

#### normalizes optimize-only requests to the standard mir level

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = normalized_options(false, true, "dev", nil)
expect(options.release).to_equal(true)
expect(options.optimize).to_equal(true)
expect(options.opt_level).to_equal(2)
```

</details>

#### preserves explicit aggressive opt levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = normalized_options(true, true, "prod", Some(3))
expect(options.release).to_equal(true)
expect(options.optimize).to_equal(true)
expect(options.opt_level).to_equal(3)
```

</details>

#### preserves explicit basic opt levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = normalized_options(false, true, "dev", Some(1))
expect(options.release).to_equal(true)
expect(options.optimize).to_equal(true)
expect(options.opt_level).to_equal(1)
expect(compileoptions_effective_mir_opt_level(options)).to_equal(1)
```

</details>

#### preserves explicit standard opt levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = normalized_options(true, true, "prod", Some(2))
expect(options.release).to_equal(true)
expect(options.optimize).to_equal(true)
expect(options.opt_level).to_equal(2)
expect(compileoptions_effective_mir_opt_level(options)).to_equal(2)
```

</details>

#### preserves explicit none while keeping release metadata intact

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = normalized_options(true, false, "prod", Some(0))
expect(options.release).to_equal(true)
expect(options.optimize).to_equal(false)
expect(options.opt_level).to_equal(0)
```

</details>

#### keeps hash-relevant effective opt levels unchanged across normalized release paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val legacy_release = normalized_options(true, false, "prod", nil)
val explicit_standard = normalized_options(true, true, "prod", Some(2))
val release_hash = compile_options_hash_compute(
    legacy_release.backend,
    legacy_release.opt_level ?? 0,
    legacy_release.release,
    legacy_release.debug_info,
    legacy_release.gc_off,
    legacy_release.profile,
    legacy_release.allowed_families
)
val explicit_hash = compile_options_hash_compute(
    explicit_standard.backend,
    explicit_standard.opt_level ?? 0,
    explicit_standard.release,
    explicit_standard.debug_info,
    explicit_standard.gc_off,
    explicit_standard.profile,
    explicit_standard.allowed_families
)
expect(release_hash.hash).to_equal(explicit_hash.hash)
expect(release_hash.opt_level).to_equal(explicit_hash.opt_level)
```

</details>

#### applies baremetal preset family restrictions to compile options

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = preset_apply_compile_options(preset_cortex_m4(), CompileOptions.default())
expect(options.gc_off).to_equal(true)
expect(options.allowed_families.len()).to_equal(2)
expect(options.allowed_families[0]).to_equal("nogc_async_mut_noalloc")
expect(options.allowed_families[1]).to_equal("common")
```

</details>

#### keeps hosted preset compile options unrestricted

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = preset_apply_compile_options(preset_linux_x86_64(), CompileOptions.default())
expect(options.gc_off).to_equal(false)
expect(options.allowed_families.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/compile_options_normalization_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compile option normalization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
