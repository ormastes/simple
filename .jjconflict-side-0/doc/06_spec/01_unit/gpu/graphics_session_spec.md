# graphics_session_spec

> Purpose: Prove that GraphicsSession API.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# graphics_session_spec

Purpose: Prove that GraphicsSession API.

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `test/01_unit/gpu/graphics_session_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that GraphicsSession API.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### GraphicsSession API

#### creates managed sessions inactive

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates managed sessions inactive
- Verify: creates managed sessions inactive
   - Expected: s.mode equals `managed_shared`
   - Expected: s.active is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("creates managed sessions inactive")
step("Verify: creates managed sessions inactive")
# @req: REQ-GPU-001
val s = GraphicsSession.make(1, "managed_shared")
expect(s.mode).to_equal("managed_shared")
expect(s.active).to_equal(false)
```

</details>

#### rejects sharing perf exclusive sessions twice

- rejects sharing perf exclusive sessions twice
- Verify: rejects sharing perf exclusive sessions twice
   - Expected: first equals ``
   - Expected: second equals `error:mode_conflict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("rejects sharing perf exclusive sessions twice")
step("Verify: rejects sharing perf exclusive sessions twice")
val s = GraphicsSession.make(2, "perf_exclusive")
val first = s.retain()
val second = s.retain()
expect(first).to_equal("")
expect(second).to_equal("error:mode_conflict")
```

</details>

#### begins a frame after retain

- begins a frame after retain
- Verify: begins a frame after retain
   - Expected: ret equals ``
   - Expected: frame equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("begins a frame after retain")
step("Verify: begins a frame after retain")
val s = GraphicsSession.make(1, "managed_shared")
val ret = s.retain()
val frame = s.begin_frame()
expect(ret).to_equal("")
expect(frame).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### GraphicsSession surfaces

#### keeps legacy 2D constructors in legacy no-session mode

- keeps legacy 2D constructors in legacy no-session mode
- Verify: keeps legacy 2D constructors in legacy no-session mode
   - Expected: e.backend equals `legacy_no_session`
   - Expected: e.fill_rect(0, 0, 100, 100, 0) equals `fill_rect`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("keeps legacy 2D constructors in legacy no-session mode")
step("Verify: keeps legacy 2D constructors in legacy no-session mode")
val e = LegacyEngine2D.create(1920, 1080)
expect(e.backend).to_equal("legacy_no_session")
expect(e.fill_rect(0, 0, 100, 100, 0)).to_equal("fill_rect")
```

</details>

#### keeps legacy 3D constructors in legacy no-session mode

- keeps legacy 3D constructors in legacy no-session mode
- Verify: keeps legacy 3D constructors in legacy no-session mode
   - Expected: e.backend equals `legacy_no_session`
   - Expected: e.draw_mesh(1, 2) equals `draw_mesh`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("keeps legacy 3D constructors in legacy no-session mode")
step("Verify: keeps legacy 3D constructors in legacy no-session mode")
val e = LegacyEngine3D.create(1280, 720)
expect(e.backend).to_equal("legacy_no_session")
expect(e.draw_mesh(1, 2)).to_equal("draw_mesh")
```

</details>

#### supports managed 2D game sprite sessions

- supports managed 2D game sprite sessions
- Verify: supports managed 2D game sprite sessions
   - Expected: g.mode equals `managed_shared`
   - Expected: g.add_sprite(10, 20, 64, 64, 1) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("supports managed 2D game sprite sessions")
step("Verify: supports managed 2D game sprite sessions")
val g = Game2DSession.create_managed(1280, 720)
expect(g.mode).to_equal("managed_shared")
expect(g.add_sprite(10, 20, 64, 64, 1)).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### supports perf-exclusive 3D game asset sessions

- supports perf-exclusive 3D game asset sessions
- Verify: supports perf-exclusive 3D game asset sessions
   - Expected: g.mode equals `perf_exclusive`
   - Expected: g.load_asset("mesh.obj", "mesh") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("supports perf-exclusive 3D game asset sessions")
step("Verify: supports perf-exclusive 3D game asset sessions")
val g = Game3DSession.create_perf(1920, 1080)
expect(g.mode).to_equal("perf_exclusive")
expect(g.load_asset("mesh.obj", "mesh")).to_equal(1)
```

</details>

#### shares managed policy across web, GUI, and WM surfaces

- shares managed policy across web, GUI, and WM surfaces
- Verify: shares managed policy across web, GUI, and WM surfaces
   - Expected: web.mode equals `managed_shared`
   - Expected: gui.mode equals `managed_shared`
   - Expected: wm.mode equals `managed_shared`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("shares managed policy across web, GUI, and WM surfaces")
step("Verify: shares managed policy across web, GUI, and WM surfaces")
val web = WebRendererSession.create_managed(1)
val gui = GuiAppSession.create_managed()
val wm = WmCompositorSession.create_managed()
expect(web.mode).to_equal("managed_shared")
expect(gui.mode).to_equal("managed_shared")
expect(wm.mode).to_equal("managed_shared")
```

</details>

### GraphicsSession optimization providers

#### persists provider facts by incrementing fact count

- persists provider facts by incrementing fact count
- Verify: persists provider facts by incrementing fact count
   - Expected: p.add_fact("simd_width", "256") equals `1`
   - Expected: p.add_fact("arch", "x86_64") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-GPU
step("persists provider facts by incrementing fact count")
step("Verify: persists provider facts by incrementing fact count")
val p = GraphicsOptProvider.create("test", "shader", "vulkan")
expect(p.add_fact("simd_width", "256")).to_equal(1)
expect(p.add_fact("arch", "x86_64")).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-GPU`
- `REQ-GPU-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ba464c756ae3f5de2ee1876bccee7be7d13807c26b69f5f1ce2cac95095b45fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ba464c756ae3f5de2ee1876bccee7be7d13807c26b69f5f1ce2cac95095b45fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ba464c756ae3f5de2ee1876bccee7be7d13807c26b69f5f1ce2cac95095b45fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/gpu/graphics_session_spec.spl
mirror: doc/06_spec/01_unit/gpu/graphics_session_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/gpu/graphics_session_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/gpu/graphics_session_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/gpu/graphics_session_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/gpu/graphics_session_spec.spl:464:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates managed sessions inactive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/gpu/graphics_session_spec.spl:473:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects sharing perf exclusive sessions twice' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/gpu/graphics_session_spec.spl:483:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'begins a frame after retain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
