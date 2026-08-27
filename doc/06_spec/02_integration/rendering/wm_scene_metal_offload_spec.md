# wm_scene_metal_offload_spec

> GUI WM Scene -> Metal GPU Offload (end-to-end)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wm_scene_metal_offload_spec

GUI WM Scene -> Metal GPU Offload (end-to-end)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/wm_scene_metal_offload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

GUI WM Scene -> Metal GPU Offload (end-to-end)

@tag: rendering, engine2d, metal, gui, draw_ir, offload, platform
@cover src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl 30%
@cover src/lib/common/ui/window_scene_draw_ir.spl 20%

Proves the Pure Simple GUI window-manager scene projects to Draw IR and renders
through the Metal-selected Engine2D, bit-exact against the CPU reference. This
closes the gap left by draw_ir_adv_spec.spl, which only exercises the "cpu"
backend with gpu_available=false and never touches the Metal GPU path.

Pipeline under test:
  WindowManager -> SharedWmScene
    -> shared_wm_scene_draw_ir_composition -> DrawIrComposition (rect + text)
    -> engine2d_draw_ir_adv_composition(Engine2D[backend=metal]) -> GPU
    -> read_pixels()

Genuine (non-mirror) GPU readback for the Metal backend is asserted separately by
scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs (which proves
read_pixels downloads the GPU framebuffer and checks gpu_frame_complete). Here we
prove the GUI composition path is correct on a real Metal device by using the CPU
backend as a bit-exact oracle.

Tests ALWAYS run. Platform-conditional assertions gate on is_macos().

## Scenarios

### GUI WM scene Metal GPU offload

#### projects the WM scene into a non-empty Draw IR composition

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- projects the WM scene into a non-empty Draw IR composition
   - Expected: comp.backend_target equals `DRAW_IR_BACKEND_GPU`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("projects the WM scene into a non-empty Draw IR composition")
val comp = _composition()
# desktop + chrome + one window batch
expect(comp.batches.len()).to_be_greater_than(2)
expect(comp.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
```

</details>

#### renders the WM composition on the CPU backend (oracle baseline)

- renders the WM composition on the CPU backend (oracle baseline)
   - Expected: cpu.backend_name() equals `cpu`
   - Expected: _nonzero(cpu.read_pixels()) equals `SCENE_W * SCENE_H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders the WM composition on the CPU backend (oracle baseline)")
var cpu = Engine2D.create_with_backend(SCENE_W, SCENE_H, "cpu")
val result = engine2d_draw_ir_adv_composition(cpu, _composition(), false)
expect(cpu.backend_name()).to_equal("cpu")
expect(result.rendered_command_count).to_be_greater_than(0)
# the desktop fill covers the whole framebuffer
expect(_nonzero(cpu.read_pixels())).to_equal(SCENE_W * SCENE_H)
```

</details>

#### Metal strict availability

#### reports Metal availability consistently with the platform

- reports Metal availability consistently with the platform
   - Expected: result.is_ok() is true
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports Metal availability consistently with the platform")
val result = Engine2D.create_with_backend_strict(16, 16, "metal")
if is_macos():
    expect(result.is_ok()).to_equal(true)
else:
    expect(result.is_ok()).to_equal(false)
```

</details>

#### on macOS: WM scene renders bit-exact on Metal GPU

#### selects the Metal backend and matches the CPU oracle pixel-for-pixel

- selects the Metal backend and matches the CPU oracle pixel-for-pixel
   - Expected: metal.backend_name() equals `metal`
   - Expected: metal_result.rendered_command_count equals `cpu_result.rendered_command_count`
   - Expected: _diffcount(cpu_px, metal_px) equals `0`
   - Expected: is_macos() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("selects the Metal backend and matches the CPU oracle pixel-for-pixel")
if is_macos():
    val comp = _composition()

    var cpu = Engine2D.create_with_backend(SCENE_W, SCENE_H, "cpu")
    val cpu_result = engine2d_draw_ir_adv_composition(cpu, comp, false)
    val cpu_px = cpu.read_pixels()

    var metal = Engine2D.create_with_backend(SCENE_W, SCENE_H, "metal")
    val metal_result = engine2d_draw_ir_adv_composition(metal, comp, true)
    val metal_px = metal.read_pixels()

    expect(metal.backend_name()).to_equal("metal")
    expect(metal_result.rendered_command_count).to_equal(cpu_result.rendered_command_count)
    expect(_nonzero(metal_px)).to_be_greater_than(0)
    # GPU offload must be bit-exact with the CPU reference render
    expect(_diffcount(cpu_px, metal_px)).to_equal(0)
else:
    # Non-macOS hosts have no Metal device; covered by the strict test.
    expect(is_macos()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4612d86ccdcf79ce7decbd4dc3a748467db36c81a63c58f7dba63fe4f13962f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4612d86ccdcf79ce7decbd4dc3a748467db36c81a63c58f7dba63fe4f13962f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4612d86ccdcf79ce7decbd4dc3a748467db36c81a63c58f7dba63fe4f13962f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/rendering/wm_scene_metal_offload_spec.spl
mirror: doc/06_spec/02_integration/rendering/wm_scene_metal_offload_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/wm_scene_metal_offload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/wm_scene_metal_offload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/wm_scene_metal_offload_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/wm_scene_metal_offload_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'projects the WM scene into a non-empty Draw IR composition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/wm_scene_metal_offload_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders the WM composition on the CPU backend (oracle baseline)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/wm_scene_metal_offload_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports Metal availability consistently with the platform' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
