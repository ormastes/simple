# gpu_cuda_programming_acceptance_spec

> These are the things someone writing GPU code in Simple must be able to do, stated

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu_cuda_programming_acceptance_spec

These are the things someone writing GPU code in Simple must be able to do, stated

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/acceptance/gpu_cuda_programming_acceptance_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

These are the things someone writing GPU code in Simple must be able to do, stated
    as outcomes rather than as calls. Scenarios that need real hardware run only under
    SIMPLE_CUDA_TEST=1 and otherwise say so out loud; a scenario that quietly passes
    without touching a device would make this whole file worthless as evidence.

## Scenarios

### A developer programs a GPU in Simple

#### discovers the machine's GPUs and what they are, with no CUDA toolkit installed

- Ask whether a CUDA driver is present at all -- this must answer on any host
- No CUDA driver on this host: report the absence rather than inventing devices
- Initialise the driver and count the devices
- Every device answers with a non-empty name and a plausible compute capability
- Compute capability is returned packed, e.g. 86 for sm_86.
- KNOWN RED: this returns -3, the no-CUDA sentinel, on a working CUDA host --


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Ask whether a CUDA driver is present at all -- this must answer on any host")
val available = cuda_available()
if not available:
    step("No CUDA driver on this host: report the absence rather than inventing devices")
    assert_equal(cuda_device_count(), 0)
else:
    step("Initialise the driver and count the devices")
    assert_equal(cuda_init(), 0)
    val count = cuda_device_count()
    assert_true(count > 0)
    step("Every device answers with a non-empty name and a plausible compute capability")
    for d in 0..count:
        assert_true(cuda_get_device_name(d).len() > 0)
        step("Compute capability is returned packed, e.g. 86 for sm_86.")
        step("KNOWN RED: this returns -3, the no-CUDA sentinel, on a working CUDA host -- " +
             "doc/08_tracking/bug/cuda_device_compute_capability_returns_nocuda_sentinel_2026-08-25.md")
        assert_true(cuda_device_compute_capability(d) > 0)
```

</details>

#### round-trips a realistically sized typed buffer through device memory without corruption

- SKIP: no device requested/available (set SIMPLE_CUDA_TEST=1 on a CUDA host)
- Select device 0 and allocate room for 2048 f32 -- the size that used to SEGV
- Upload a pattern that includes negative values, then read it back
- The same guarantee holds for integer buffers


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not device_present():
    step("SKIP: no device requested/available (set SIMPLE_CUDA_TEST=1 on a CUDA host)")
    assert_true(true)
else:
    step("Select device 0 and allocate room for 2048 f32 -- the size that used to SEGV")
    assert_true(gpu_set_device(0).is_ok())
    val n = 2048
    val buf = gpu_alloc(n * 4).unwrap()
    step("Upload a pattern that includes negative values, then read it back")
    val sent = [for i in 0..n: (i as f32) - 1024.0]
    assert_true(gpu_upload_f32(buf, sent).is_ok())
    val got = gpu_download_f32(buf, n).unwrap()
    assert_equal(got.len(), n)
    assert_equal(got[0], sent[0])
    assert_equal(got[1024], sent[1024])
    assert_equal(got[n - 1], sent[n - 1])
    assert_true(gpu_free(buf).is_ok())

step("The same guarantee holds for integer buffers")
if device_present():
    val m = 512
    val ibuf = gpu_alloc(m * 4).unwrap()
    val isent = [for i in 0..m: i - 256]
    assert_true(gpu_upload_i32(ibuf, isent).is_ok())
    val igot = gpu_download_i32(ibuf, m).unwrap()
    assert_equal(igot[0], isent[0])
    assert_equal(igot[m - 1], isent[m - 1])
    assert_true(gpu_free(ibuf).is_ok())
```

</details>

#### develops and verifies 2-D kernel index arithmetic with no GPU present

- Run the real kernel body over a 2x2 grid of 3x2 blocks -- a 6x4 matrix
- Every work-item ran: 4 blocks x 6 threads
- The flat indices cover 0..23 exactly once -- the kernel's addressing is correct
- Grid and block extents are visible to the kernel in all three dimensions
- After the launch the executor is back to single-thread defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the real kernel body over a 2x2 grid of 3x2 blocks -- a 6x4 matrix")
_flat = []
_cols = 6
val executed = gpu_launch_emulated((2, 2, 1), (3, 2, 1), record_row_major)
step("Every work-item ran: 4 blocks x 6 threads")
assert_equal(executed, 24)
assert_equal(_flat.len(), 24)
step("The flat indices cover 0..23 exactly once -- the kernel's addressing is correct")
var i = 0
while i < 24:
    var seen = 0
    for v in _flat:
        if v == i: seen = seen + 1
    assert_equal(seen, 1)
    i = i + 1
step("Grid and block extents are visible to the kernel in all three dimensions")
_flat = []
assert_equal(gpu_launch_emulated((1, 3, 2), (2, 1, 4), record_row_major), 48)
step("After the launch the executor is back to single-thread defaults")
assert_equal(gpu_grid_dim_y(), 1)
assert_equal(gpu_block_dim_z(), 1)
```

</details>

#### guards the tail of a 1-D range so a kernel never runs past its data

- 10 elements at block size 4 dispatch 3 blocks, but only 10 work-items run
- An empty or malformed range executes nothing rather than guessing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("10 elements at block size 4 dispatch 3 blocks, but only 10 work-items run")
_ticks = 0
assert_equal(cpu_kernel_run_1d(10, 4, tick), 10)
assert_equal(_ticks, 10)
step("An empty or malformed range executes nothing rather than guessing")
assert_equal(cpu_kernel_run_1d(0, 4, tick), 0)
assert_equal(gpu_launch_emulated((1, 1, 1), (0, 1, 1), tick), 0)
```

</details>

#### tells the truth when a backend is unavailable instead of faking a pass

- Probe the Metal lane; on a non-macOS host this must be a machine-readable skip
- Reported unavailable with a reason: {verdict}
- Metal is genuinely available here, so the probe must not claim otherwise


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Probe the Metal lane; on a non-macOS host this must be a machine-readable skip")
val verdict = MetalLaneSession.create().probe()
if verdict.starts_with("skip:"):
    step("Reported unavailable with a reason: {verdict}")
    assert_true(verdict.starts_with("skip:metal-unavailable"))
else:
    step("Metal is genuinely available here, so the probe must not claim otherwise")
    assert_equal(verdict, "")
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
