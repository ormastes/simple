# Engine Platform Specification

> 1. var engine = Engine2D create

<!-- sdn-diagram:id=engine_platform_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_platform_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_platform_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_platform_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Platform Specification

## Scenarios

### Engine2D

### create (updated)

#### creates an engine through auto backend detection

1. var engine = Engine2D create
   - Expected: engine.width() equals `4`
   - Expected: engine.height() equals `4`
2. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine2D.create(4, 4)

expect(engine.backend_name().len()).to_be_greater_than(0)
expect(engine.width()).to_equal(4)
expect(engine.height()).to_equal(4)
engine.shutdown()
```

</details>

#### AC-7: uses platform-aware detection

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-8: accepts optional FfiMode

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### create_with_backend (updated)

#### AC-5: supports qualcomm backend name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-1: vulkan backend still selectable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-2: cuda backend still selectable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-3: rocm backend selectable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-4: intel backend selectable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

### compute dispatch

#### exposes best compute backend without replacing render backend selection

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Engine2D.create_compute_dispatch()

expect(_valid_compute_backend_name(result.selected_name)).to_equal(true)
expect(result.probe.has_compute).to_equal(true)
expect(result.probe.status == BackendStatus.Initialized).to_equal(true)
expect(Engine2D.detect_best_compute_backend()).to_equal(result.selected_name)
```

</details>

#### routes explicit compute backends through strict factory diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu = Engine2D.create_compute_dispatch_for_backend("cpu")
val missing = Engine2D.create_compute_dispatch_for_backend("missing_compute_backend")

expect(cpu.selected_name).to_equal("cpu")
expect(cpu.is_available()).to_equal(true)
expect(missing.is_available()).to_equal(false)
expect(missing.probe.status == BackendStatus.Failed).to_equal(true)
```

</details>

#### keeps explicit GPU compute diagnostics on requested backends

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cuda = Engine2D.create_compute_dispatch_for_backend("cuda")
val rocm = Engine2D.create_compute_dispatch_for_backend("rocm")
val opencl = Engine2D.create_compute_dispatch_for_backend("opencl")

expect(cuda.selected_name).to_equal("cuda")
expect(cuda.probe.has_compute).to_equal(true)
expect(cuda.probe.shader_format).to_equal("ptx")
expect(rocm.selected_name).to_equal("rocm")
expect(rocm.probe.has_compute).to_equal(true)
expect(rocm.probe.shader_format).to_equal("hsaco")
expect(opencl.selected_name).to_equal("opencl")
expect(opencl.probe.has_compute).to_equal(true)
expect(opencl.probe.shader_format).to_equal("opencl-c")
```

</details>

#### exposes dispatch summary evidence through the Engine2D accessor path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Engine2D.create_compute_dispatch()

expect(result.summary()).to_contain("dispatch selected=")
expect(result.summary()).to_contain("probe=requested=")
```

</details>

### FFI dispatch mode

#### AC-8: dynamic mode tries dlopen first

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-8: static mode uses extern fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

#### AC-8: fallback to CPU when no GPU backend available

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/engine_platform_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine2D
- create (updated)
- create_with_backend (updated)
- compute dispatch
- FFI dispatch mode

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
