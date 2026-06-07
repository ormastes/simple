# Linker Specification

> <details>

<!-- sdn-diagram:id=linker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linker_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linker Specification

## Scenarios

### Linker

#### uses expected default link configuration

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LinkConfig.default()
expect(config.output_format).to_equal(OutputFormat.Smf)
expect(config.output_path).to_equal("a.out")
expect(config.pie).to_equal(true)
expect(config.verbose).to_equal(false)
expect(config.allow_deferred).to_equal(false)
```

</details>

#### creates native and smf configs

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val native_cfg = LinkConfig.native("output.bin")
val smf_cfg = LinkConfig.smf("output.smf")

expect(native_cfg.output_format).to_equal(OutputFormat.Native)
expect(native_cfg.output_path).to_equal("output.bin")
expect(smf_cfg.output_format).to_equal(OutputFormat.Smf)
expect(smf_cfg.output_path).to_equal("output.smf")
```

</details>

#### initializes linker state and shared defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val linker = Linker.new(LinkConfig.default())
val stats_cfg = objtakerconfig_default()

expect(linker.readers.len()).to_equal(0)
expect(linker.symbols.len()).to_equal(0)
expect(linker.errors.len()).to_equal(0)
expect(linker.obj_taker.config.max_cache_size).to_equal(stats_cfg.max_cache_size)
expect(linker.config.output_format).to_equal(OutputFormat.Smf)
```

</details>

#### keeps mold and module loader defaults aligned with the current pipeline

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mold_cfg = MoldConfig.default()
val loader_cfg = ModuleLoaderConfig.default()
val loader = ModuleLoader.with_defaults()

expect(mold_cfg.pie).to_equal(true)
expect(mold_cfg.verbose).to_equal(false)
expect(loader_cfg.enable_jit).to_equal(true)
expect(loader_cfg.enable_cache).to_equal(true)
expect(loader.stats().module_count).to_equal(0)
expect(loader.stats().symbol_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/linker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Linker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
