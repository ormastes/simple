# gpu_launch_emulated_3d_spec

> Purpose: prove `gpu_launch_emulated(grid, block, kernel)` gives the host meaning of

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu_launch_emulated_3d_spec

Purpose: prove `gpu_launch_emulated(grid, block, kernel)` gives the host meaning of

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/gpu_launch_emulated_3d_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose: prove `gpu_launch_emulated(grid, block, kernel)` gives the host meaning of
`kernel<<<grid, block>>>()` — every builtin id/dim reflects the current work-item in all
three dimensions, and a 2-D index scheme reproduces a CPU reference. Device-free.
Audience: GPU stdlib maintainers; tutorial authors using CPU emulation in doctests.
Plan: doc/03_plan/lib/gpu/gpu_cuda_hardening_plan_2026-08-25.md row E1.

## Scenarios

### gpu_launch_emulated — 3-D host executor for <<<grid, block>>>

#### visits every work-item of a 2-D grid x 2-D block exactly once, in a full row-major cover

- grid (2,2,1) x block (3,2,1) = 4 blocks x 6 threads = 24 items covering a 6x4 matrix
- every flat index 0..23 appears exactly once


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("grid (2,2,1) x block (3,2,1) = 4 blocks x 6 threads = 24 items covering a 6x4 matrix")
_seen = []
_cols = 2 * 3
_rows = 2 * 2
val executed = gpu_launch_emulated((2, 2, 1), (3, 2, 1), record_flat_2d)
assert_equal(executed, 24)
assert_equal(_seen.len(), 24)
step("every flat index 0..23 appears exactly once")
var i = 0
while i < 24:
    var count = 0
    for s in _seen:
        if s == i: count = count + 1
    assert_equal(count, 1)
    i = i + 1
```

</details>

#### exposes grid/block dims and z ids to the kernel, and restores single-thread defaults after

- first item sees grid (1,2,3) and block (4,1,2)
- the last item is block z=2, local z=1
- state is reset: ids 0, dims 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_seen = []
val executed = gpu_launch_emulated((1, 2, 3), (4, 1, 2), record_dims_3d)
assert_equal(executed, 1 * 2 * 3 * 4 * 1 * 2)
step("first item sees grid (1,2,3) and block (4,1,2)")
assert_equal(_seen[0], 123)
assert_equal(_seen[1], 412)
step("the last item is block z=2, local z=1")
assert_equal(_seen[_seen.len() - 1], 201)
step("state is reset: ids 0, dims 1")
assert_equal(gpu_global_id_z(), 0)
assert_equal(gpu_block_id_y(), 0)
assert_equal(gpu_grid_dim_y(), 1)
assert_equal(gpu_block_dim_z(), 1)
```

</details>

#### rejects invalid shapes with 0 executed and matches cpu_kernel_run_1d for a 1-D launch

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(gpu_launch_emulated((0, 1, 1), (1, 1, 1), record_dims_3d), 0)
assert_equal(gpu_launch_emulated((1, 1, 1), (1, -1, 1), record_dims_3d), 0)
_seen = []
_cols = 8
val via_3d = gpu_launch_emulated((2, 1, 1), (4, 1, 1), record_flat_2d)
val seen_3d = _seen
_seen = []
val via_1d = cpu_kernel_run_1d(8, 4, record_flat_2d)
assert_equal(via_3d, via_1d)
assert_equal(seen_3d, _seen)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
