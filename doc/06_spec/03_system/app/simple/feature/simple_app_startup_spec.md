# Simple App Startup Specification

> <details>

<!-- sdn-diagram:id=simple_app_startup_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_app_startup_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_app_startup_spec -> std
simple_app_startup_spec -> app
simple_app_startup_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_app_startup_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple App Startup Specification

## Scenarios

### simple app startup metadata

### REQ-001: launch kind detection

#### should classify SMF files as SMF launches

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(startup_detect_launch_kind("tool.smf")).to_equal("smf")
expect(startup_detect_launch_kind("TOOL.SMF")).to_equal("smf")
```

</details>

#### should classify Simple source files as script launches

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(startup_detect_launch_kind("main.spl")).to_equal("script")
expect(startup_detect_launch_kind("run.shs")).to_equal("script")
```

</details>

#### should classify other executable files as native launches

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(startup_detect_launch_kind("simple")).to_equal("native")
expect(startup_detect_launch_kind("app.bin")).to_equal("native")
```

</details>

### REQ-002: file argument parsing

#### should add the entry path as argv zero when missing

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = startup_normalize_program_args("main.spl", ["one", "two"])
expect(args[0]).to_equal("main.spl")
expect(args[1]).to_equal("one")
expect(args[2]).to_equal("two")
```

</details>

#### should not duplicate argv zero when caller already passed it

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = startup_normalize_program_args("main.spl", ["main.spl", "one"])
expect(args.len()).to_equal(2)
expect(args[0]).to_equal("main.spl")
expect(args[1]).to_equal("one")
```

</details>

#### should exclude app arg parser code when metadata says the app does not use it

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = _metadata("native", false, false, [], [])
val plan = startup_plan_from_metadata("native_app", ["--unused"], metadata, true, false)
expect(plan.include_arg_parser).to_equal(false)
expect(startup_feature_summary(plan)).to_contain("arg_parser=false")
```

</details>

### REQ-003: mmap or cache strategy

#### should use host mmap when metadata requests cache and host supports mmap

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = _metadata("script", true, true, [], [])
val plan = startup_plan_from_metadata("main.spl", [], metadata, true, false)
expect(plan.include_mmap_cache).to_equal(true)
expect(plan.cache_strategy).to_equal("mmap")
```

</details>

#### should use SimpleOS VFS prewarm when host mmap is unavailable

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = _metadata("smf", true, true, [], [])
val plan = startup_plan_from_metadata("app.smf", [], metadata, false, true)
expect(plan.include_mmap_cache).to_equal(true)
expect(plan.cache_strategy).to_equal("simpleos_vfs_prewarm")
```

</details>

#### should make SimpleOS app metadata use the SimpleOS VFS prewarm lane

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = launch_metadata_for_simpleos_path("/sys/apps/simple.smf")
val plan = startup_plan_from_metadata("/sys/apps/simple.smf", [], metadata, false, true)
expect(plan.target_os).to_equal("simpleos")
expect(plan.include_mmap_cache).to_equal(true)
expect(plan.cache_strategy).to_equal("simpleos_vfs_prewarm")
expect(startup_feature_summary(plan)).to_contain("os=simpleos")
```

</details>

#### should fall back to normal read when no cache support is available

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = _metadata("script", true, true, [], [])
val plan = startup_plan_from_metadata("main.spl", [], metadata, false, false)
expect(plan.include_mmap_cache).to_equal(false)
expect(plan.cache_strategy).to_equal("normal_read")
```

</details>

### REQ-004: conditional dynlib loading

#### should include no dynlib loader when no dependencies are declared

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = _metadata("native", false, false, [], [])
val plan = startup_plan_from_metadata("native_app", [], metadata, true, false)
expect(plan.include_dynlib_loader).to_equal(false)
expect(plan.load_native_dynlibs.len()).to_equal(0)
expect(plan.load_smf_dynlibs.len()).to_equal(0)
```

</details>

#### should load native dynlibs declared by native build metadata

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = _metadata("native", false, false, ["libsimple_gui.dylib"], [])
val plan = startup_plan_from_metadata("native_app", [], metadata, true, false)
expect(plan.include_dynlib_loader).to_equal(true)
expect(plan.load_native_dynlibs[0]).to_equal("libsimple_gui.dylib")
```

</details>

#### should load SMF dynlibs declared by SMF metadata

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = _metadata("smf", true, true, [], ["/sys/lib/gui_hot.smf"])
val plan = startup_plan_from_metadata("app.smf", ["app.smf"], metadata, true, false)
expect(plan.include_dynlib_loader).to_equal(true)
expect(plan.load_smf_dynlibs[0]).to_equal("/sys/lib/gui_hot.smf")
expect(plan.program_args[0]).to_equal("app.smf")
```

</details>

### REQ-005: build launch metadata sidecar

#### should render native build launch metadata as a sidecar

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = launch_metadata_for_native_build("host", "x86_64", "native")
val sidecar = render_launch_metadata_sidecar(metadata)
expect(sidecar).to_contain("simple_launch_metadata:")
expect(sidecar).to_contain("entry_kind: \"native\"")
expect(sidecar).to_contain("uses_arg_parser: false")
expect(sidecar).to_contain("mmap_hint: false")
```

</details>

#### should parse sidecar metadata with native and SMF dynlib dependencies

<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sidecar =
    "simple_launch_metadata:\n" +
    "  entry_kind: \"smf\"\n" +
    "  target_os: \"simpleos\"\n" +
    "  target_arch: \"x86_64\"\n" +
    "  target_abi: \"simpleos\"\n" +
    "  uses_arg_parser: true\n" +
    "  mmap_hint: true\n" +
    "  native_dynlib: \"libhost_gui.dylib\"\n" +
    "  smf_dynlib: \"/sys/lib/gui_hot.smf\"\n"
val metadata = parse_launch_metadata_sidecar(sidecar, "native")
val plan = startup_plan_from_metadata("app.smf", ["app.smf"], metadata, false, true)
expect(metadata.entry_kind).to_equal("smf")
expect(metadata.target_os).to_equal("simpleos")
expect(plan.include_dynlib_loader).to_equal(true)
expect(plan.load_native_dynlibs[0]).to_equal("libhost_gui.dylib")
expect(plan.load_smf_dynlibs[0]).to_equal("/sys/lib/gui_hot.smf")
expect(plan.cache_strategy).to_equal("simpleos_vfs_prewarm")
```

</details>

#### should name sidecars next to the artifact path

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(launch_metadata_sidecar_path("build/app")).to_equal("build/app.simple_launch.sdn")
```

</details>

### REQ-006: embedded SMF launch metadata

#### should parse embedded SMF metadata for SimpleOS startup

1. var opts = SmfBuildOptions create

2. opts launch metadata bytes = sidecar bytes
   - Expected: metadata.entry_kind equals `smf`
   - Expected: metadata.target_os equals `simpleos`
   - Expected: plan.include_arg_parser is true
   - Expected: plan.include_mmap_cache is true
   - Expected: plan.cache_strategy equals `simpleos_vfs_prewarm`
   - Expected: plan.include_dynlib_loader is true
   - Expected: plan.load_smf_dynlibs[0] equals `/sys/lib/gui_hot.smf`
   - Expected: plan.program_args[0] equals `/sys/apps/simple.smf`


<details>
<summary>Executable SPipe</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var opts = SmfBuildOptions.create(Target.x86_64_unknown_linux_gnu())
val sidecar =
    "simple_launch_metadata:\n" +
    "  entry_kind: \"smf\"\n" +
    "  target_os: \"simpleos\"\n" +
    "  target_arch: \"multiarch\"\n" +
    "  target_abi: \"simpleos\"\n" +
    "  uses_arg_parser: true\n" +
    "  mmap_hint: true\n" +
    "  smf_dynlib: \"/sys/lib/gui_hot.smf\"\n"
opts.launch_metadata_bytes = sidecar.bytes()

val smf = generate_smf_with_options([0xC3], opts)
val metadata = parse_launch_metadata_from_smf_bytes(smf, "smf")
val plan = startup_plan_from_metadata("/sys/apps/simple.smf", ["--open", "doc.spl"], metadata, false, true)

expect(metadata.entry_kind).to_equal("smf")
expect(metadata.target_os).to_equal("simpleos")
expect(plan.include_arg_parser).to_equal(true)
expect(plan.include_mmap_cache).to_equal(true)
expect(plan.cache_strategy).to_equal("simpleos_vfs_prewarm")
expect(plan.include_dynlib_loader).to_equal(true)
expect(plan.load_smf_dynlibs[0]).to_equal("/sys/lib/gui_hot.smf")
expect(plan.program_args[0]).to_equal("/sys/apps/simple.smf")
```

</details>

### REQ-007: embedded native launch metadata

#### should parse native launch metadata from the binary trailer

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metadata = launch_metadata_for_native_build("macos", "aarch64", "macho")
val binary = [0xCF, 0xFA, 0xED, 0xFE].concat(render_native_launch_metadata_trailer(metadata))
val parsed = parse_launch_metadata_from_native_bytes(binary, "native")
val plan = startup_plan_from_metadata("build/app", [], parsed, true, false)

expect(has_native_launch_metadata_trailer(binary)).to_equal(true)
expect(parsed.entry_kind).to_equal("native")
expect(parsed.target_os).to_equal("macos")
expect(parsed.target_arch).to_equal("aarch64")
expect(parsed.target_abi).to_equal("macho")
expect(plan.include_arg_parser).to_equal(false)
expect(plan.include_mmap_cache).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple/feature/simple_app_startup_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- simple app startup metadata
- REQ-001: launch kind detection
- REQ-002: file argument parsing
- REQ-003: mmap or cache strategy
- REQ-004: conditional dynlib loading
- REQ-005: build launch metadata sidecar
- REQ-006: embedded SMF launch metadata
- REQ-007: embedded native launch metadata

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
