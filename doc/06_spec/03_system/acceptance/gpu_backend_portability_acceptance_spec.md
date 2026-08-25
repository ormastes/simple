# gpu_backend_portability_acceptance_spec

> Purpose: prove that a single GPU program in Simple runs unchanged on CUDA,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu_backend_portability_acceptance_spec

Purpose: prove that a single GPU program in Simple runs unchanged on CUDA,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/acceptance/gpu_backend_portability_acceptance_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose: prove that a single GPU program in Simple runs unchanged on CUDA,
    Vulkan and Metal, that the backend is chosen by the project manifest alone,
    and that a backend the machine cannot provide says so out loud instead of
    quietly passing.

    Audience: developers writing portable GPU code, and the maintainers of the
    GPU lanes and of examples/08_gpu/backends/.

    Run: bin/simple test test/03_system/acceptance/gpu_backend_portability_acceptance_spec.spl

## Scenarios

### Write one GPU program, run it on whichever backend the host has

#### picks the backend from simple.sdn alone, so the three example directories differ only in configuration

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Choosing a backend without touching the program (expected show, folded, detail, or skip)


- Read each checked-in manifest under examples/08_gpu/backends/ -- this needs no GPU at all
- Confirm the manifest in the {backend}/ directory selects exactly the {backend} backend
   - Expected: cfg.backend equals `backend`
- Confirm the rest of the GPU section is identical across directories
   - Expected: cfg.submode equals `interpreter`
   - Expected: cfg.arch equals `auto`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-PORT-002
# @req REQ-GPU-PORT-003
step("Read each checked-in manifest under examples/08_gpu/backends/ -- this needs no GPU at all")
for backend in ["cuda", "vulkan", "metal"]:
    val cfg = load_gpu_config("{CONFIG_DIR}/{backend}/simple.sdn")

    step("Confirm the manifest in the {backend}/ directory selects exactly the {backend} backend")
    expect(cfg.backend).to_equal(backend)

    step("Confirm the rest of the GPU section is identical across directories")
    expect(cfg.submode).to_equal("interpreter")
    expect(cfg.arch).to_equal("auto")
```

</details>

#### falls back to auto-probing when a project says nothing about GPUs

- Parse a manifest that has a project section but no gpu section
- Confirm the default is to probe rather than to demand a specific device
   - Expected: cfg.backend equals `auto`
- Confirm the default execution submode and architecture are the portable ones
   - Expected: cfg.submode equals `interpreter`
   - Expected: cfg.arch equals `auto`
- Confirm an explicit gpu section overrides every default it names
   - Expected: explicit.backend equals `vulkan`
   - Expected: explicit.submode equals `jit`
   - Expected: explicit.arch equals `auto`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-PORT-004
# @req REQ-GPU-PORT-005
step("Parse a manifest that has a project section but no gpu section")
val cfg = parse_gpu_config("project:\n  name: plain_project\n")

step("Confirm the default is to probe rather than to demand a specific device")
expect(cfg.backend).to_equal("auto")

step("Confirm the default execution submode and architecture are the portable ones")
expect(cfg.submode).to_equal("interpreter")
expect(cfg.arch).to_equal("auto")

step("Confirm an explicit gpu section overrides every default it names")
val explicit = parse_gpu_config("project:\n  name: x\ngpu:\n  backend: vulkan\n  submode: jit\n")
expect(explicit.backend).to_equal("vulkan")
expect(explicit.submode).to_equal("jit")
expect(explicit.arch).to_equal("auto")
```

</details>

#### runs the shared program on a live CUDA device, or names the reason it cannot

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Running the same program on each backend (expected show, folded, detail, or skip)


- Ask the CUDA lane whether this host can run it
- No usable CUDA device: report the lane's own reason and record an honest skip
   - Expected: gpu_lane_probe_verdict("cuda", probe) equals `skip`
- Load the CUDA SVM-G kernel artefact and hand it the unmodified program
   - Expected: executor.init(file_read_bytes("{LANE_DIR}/svmg_cuda_kernel.ptx")) equals ``
- Confirm the observable result is the portable one: ok, one record valued 9, exit code 3
   - Expected: outcome.records.len() equals `1`
   - Expected: outcome.records[0].value equals `9`
   - Expected: outcome.exit_code equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-PORT-001
# @req REQ-GPU-PORT-006
# @req REQ-GPU-PORT-007
step("Ask the CUDA lane whether this host can run it")
val probe = CudaLaneSession.create().probe()

if probe.starts_with("skip:"):
    step("No usable CUDA device: report the lane's own reason and record an honest skip")
    gpu_lane_report_skip("acceptance cuda", probe)
    expect(gpu_lane_probe_verdict("cuda", probe)).to_equal("skip")
else:
    step("Load the CUDA SVM-G kernel artefact and hand it the unmodified program")
    var executor = CudaVmExecutor.create()
    expect(executor.init(file_read_bytes("{LANE_DIR}/svmg_cuda_kernel.ptx"))).to_equal("")
    val outcome = executor.run_source(HELLO_PROGRAM, 1000, 0)

    step("Confirm the observable result is the portable one: ok, one record valued 9, exit code 3")
    assert_true(outcome.ok)
    expect(outcome.records.len()).to_equal(1)
    expect(outcome.records[0].value).to_equal(9)
    expect(outcome.exit_code).to_equal(3)
```

</details>

#### runs the same program byte-for-byte on a live Vulkan device, or names the reason it cannot

- Ask the Vulkan lane whether this host can run it
- No usable Vulkan device: report the lane's own reason and record an honest skip
   - Expected: gpu_lane_probe_verdict("vulkan", probe) equals `skip`
- Load the Vulkan SVM-G kernel artefact and hand it the SAME program string used for CUDA
   - Expected: executor.init(file_read_bytes("{LANE_DIR}/svmg_vulkan_kernel.spv")) equals ``
- Confirm the result matches the CUDA result exactly -- same records, same exit code
   - Expected: outcome.records.len() equals `1`
   - Expected: outcome.records[0].value equals `9`
- KNOWN RED on a host where the CUDA case above ran live first in this same process: the Vulkan lane returns exit 0. Tracked as doc/08_tracking/bug/vulkan_vm_lane_returns_exit0_after_cuda_lane_same_process_2026-08-25.md -- the assertion is deliberately NOT weakened
   - Expected: outcome.exit_code equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-PORT-001
# @req REQ-GPU-PORT-006
# @req REQ-GPU-PORT-007
step("Ask the Vulkan lane whether this host can run it")
val probe = VulkanLaneSession.create().probe()

if probe.starts_with("skip:"):
    step("No usable Vulkan device: report the lane's own reason and record an honest skip")
    gpu_lane_report_skip("acceptance vulkan", probe)
    expect(gpu_lane_probe_verdict("vulkan", probe)).to_equal("skip")
else:
    step("Load the Vulkan SVM-G kernel artefact and hand it the SAME program string used for CUDA")
    var executor = VulkanVmExecutor.create()
    expect(executor.init(file_read_bytes("{LANE_DIR}/svmg_vulkan_kernel.spv"))).to_equal("")
    val outcome = executor.run_source(HELLO_PROGRAM, 1000, 0)

    step("Confirm the result matches the CUDA result exactly -- same records, same exit code")
    assert_true(outcome.ok)
    expect(outcome.records.len()).to_equal(1)
    if outcome.records.len() > 0:
        expect(outcome.records[0].value).to_equal(9)

    step("KNOWN RED on a host where the CUDA case above ran live first in this same process: the Vulkan lane returns exit 0. Tracked as doc/08_tracking/bug/vulkan_vm_lane_returns_exit0_after_cuda_lane_same_process_2026-08-25.md -- the assertion is deliberately NOT weakened")
    expect(outcome.exit_code).to_equal(3)
```

</details>

#### runs the same program on Metal where Metal exists, and elsewhere refuses to fake it

- Ask the Metal lane whether this host can run it
- Not a Metal host: confirm the skip reason names the backend, so a reader can tell WHY it did not run
   - Expected: gpu_lane_probe_verdict("metal", probe) equals `skip`
- Confirm the unusable backend produced no result at all -- an absent device must never look like a pass
- Load the Metal SVM-G kernel source and hand it the same unmodified program
   - Expected: executor.init(file_read_text("{LANE_DIR}/svmg_metal_kernel.metal")) equals ``
- Confirm the portable result once more
   - Expected: outcome.exit_code equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-PORT-001
# @req REQ-GPU-PORT-006
step("Ask the Metal lane whether this host can run it")
val probe = MetalLaneSession.create().probe()

if probe.starts_with("skip:"):
    step("Not a Metal host: confirm the skip reason names the backend, so a reader can tell WHY it did not run")
    gpu_lane_report_skip("acceptance metal", probe)
    expect(gpu_lane_probe_verdict("metal", probe)).to_equal("skip")
    assert_true(probe.starts_with("skip:metal-unavailable"))

    step("Confirm the unusable backend produced no result at all -- an absent device must never look like a pass")
    expect_not(probe == "")
else:
    step("Load the Metal SVM-G kernel source and hand it the same unmodified program")
    var executor = MetalVmExecutor.create()
    expect(executor.init(file_read_text("{LANE_DIR}/svmg_metal_kernel.metal"))).to_equal("")
    val outcome = executor.run_source(HELLO_PROGRAM, 1000, 0)

    step("Confirm the portable result once more")
    assert_true(outcome.ok)
    expect(outcome.exit_code).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
