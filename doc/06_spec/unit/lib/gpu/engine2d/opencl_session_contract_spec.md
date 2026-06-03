# Opencl Session Contract Specification

> <details>

<!-- sdn-diagram:id=opencl_session_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=opencl_session_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

opencl_session_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=opencl_session_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Opencl Session Contract Specification

## Scenarios

### OpenClSession compute contract

#### reports OpenCL kind and unavailable without an injected ICD FFI

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = OpenClSession.create()

expect(session.kind() == BackendSessionKind.OpenCl).to_equal(true)
expect(session.is_available()).to_equal(false)
expect(session.is_valid()).to_equal(false)
```

</details>

#### fails closed when initializing or launching without OpenCL FFI

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = OpenClSession.create()

expect(session.init()).to_equal(1)
expect(session.load_module("")).to_equal(0)
expect(session.synchronize()).to_equal(1)
expect(session.launch_kernel("simple_2d_fill_u32", 1, 1, 1, 1)).to_equal(1)
expect(session.fill_kernel(64, 64, 4096)).to_equal(1)
expect(session.copy_kernel(64, 64, 4096)).to_equal(1)
expect(session.alpha_blend_kernel(64, 64, 4096)).to_equal(1)
expect(session.scroll_kernel(64, 64, 4096)).to_equal(1)
```

</details>

#### shutdown is safe on an uninitialized session

1. var session = OpenClSession create

2. session shutdown
   - Expected: session.is_valid() is false
   - Expected: session.ref_count equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = OpenClSession.create()

session.shutdown()
expect(session.is_valid()).to_equal(false)
expect(session.ref_count).to_equal(0)
```

</details>

#### retains and releases shared OpenCL sessions like CUDA sessions

1. var session = OpenClSession create
   - Expected: retained.ref_count equals `2`
   - Expected: session.is_valid() is true

2. session release
   - Expected: session.ref_count equals `1`
   - Expected: session.context equals `2`
   - Expected: session.queue equals `3`

3. session release
   - Expected: session.ref_count equals `0`
   - Expected: session.is_valid() is false
   - Expected: session.platform equals `0`
   - Expected: session.context equals `0`
   - Expected: session.queue equals `0`
   - Expected: session.program equals `0`
   - Expected: session.kernel_cache equals `0`
   - Expected: session.generation equals `generation_before + 1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = OpenClSession.create()
session.platform = 1
session.context = 2
session.queue = 3
session.program = 4
session.kernel_cache = 5
session.is_initialized = true
session.ref_count = 1
val generation_before = session.generation

val retained = session.retain()
expect(retained.ref_count).to_equal(2)
expect(session.is_valid()).to_equal(true)

session.release()
expect(session.ref_count).to_equal(1)
expect(session.context).to_equal(2)
expect(session.queue).to_equal(3)

session.release()
expect(session.ref_count).to_equal(0)
expect(session.is_valid()).to_equal(false)
expect(session.platform).to_equal(0)
expect(session.context).to_equal(0)
expect(session.queue).to_equal(0)
expect(session.program).to_equal(0)
expect(session.kernel_cache).to_equal(0)
expect(session.generation).to_equal(generation_before + 1)
```

</details>

#### cleans up through injected OpenCL FFI release hooks

1. var session = OpenClSession create with ffi

2. session release
   - Expected: session.ref_count equals `0`
   - Expected: session.is_valid() is false
   - Expected: session.context equals `0`
   - Expected: session.queue equals `0`
   - Expected: session.program equals `0`
   - Expected: session.kernel_cache equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = OpenClSession.create_with_ffi(OpenClFfi.create_static())
session.platform = 1
session.context = 2
session.queue = 3
session.program = 4
session.kernel_cache = 5
session.is_initialized = true
session.ref_count = 1

session.release()

expect(session.ref_count).to_equal(0)
expect(session.is_valid()).to_equal(false)
expect(session.context).to_equal(0)
expect(session.queue).to_equal(0)
expect(session.program).to_equal(0)
expect(session.kernel_cache).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gpu/engine2d/opencl_session_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- OpenClSession compute contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
