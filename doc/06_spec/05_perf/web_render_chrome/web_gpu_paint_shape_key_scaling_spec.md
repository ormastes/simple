# Web GPU paint shape-key scaling

> GPU-paint timing keys retain the exact ordered `x,y,w,h;` geometry bytes,
> while construction scales linearly instead of repeatedly copying every
> accumulated prefix.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 1 | 0 | 0 | 1 |

## Scope and evidence boundary

The executable scenario is
`test/05_perf/web_render_chrome/web_gpu_paint_shape_key_scaling_spec.spl`.
It traces NFR-WEB-BROWSER-015 and NFR-WEB-BROWSER-016.

The fixture invokes only the production shape-key builder over deterministic
`SceneCommand` arrays. It does not initialize a GPU, renderer, layout engine,
device, readback, or timing-choice cache. The checked-in scenario and source
are static evidence only: no performance PASS, runtime result, bootstrap,
seed, stale artifact, or docgen result is claimed.

## Scenario

### should preserve exact identity with linear N to 2N construction

1. **Build deterministic N and 2N fill frames**
   - `make_web_gpu_shape_key_frame`
   - Build exactly 4,096 and 8,192 ordered fill commands without rendering.

2. **Preserve exact geometry cache identity**
   - `expect_web_gpu_shape_key_identity`
   - Require the exact two-record string `0,0,1,1;1,1,2,2;`.
   - Require repeated input equality and one-coordinate inequality.

3. **Measure isolated shape-key construction**
   - `web_gpu_shape_key_sample_nanos`
   - Warm once, then retain exactly nine monotonic nanosecond samples per size.

4. **Require linear N to 2N scaling**
   - `expect_web_gpu_shape_key_linear_scaling`
   - Sort each nine-sample set and require the 2N median to be less than three
     times the N median plus one nanosecond (the inclusive-equivalent bound).

<details>
<summary>Executable SSpec</summary>

The complete four-step scenario and helper implementations are retained at
`test/05_perf/web_render_chrome/web_gpu_paint_shape_key_scaling_spec.spl`.

</details>
