# SimpleOS GUI Shared WM Adapter Spec

> Focused proof that the SimpleOS GUI adapter uses the shared WM bridge,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS GUI Shared WM Adapter Spec

Focused proof that the SimpleOS GUI adapter uses the shared WM bridge,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused proof that the SimpleOS GUI adapter uses the shared WM bridge,
input, and framebuffer render path instead of only reporting capability names.

## Scenarios

### SimpleOS GUI adapter shared WM proof

#### routes bridge, input, and framebuffer presentation through HostCompositor

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes bridge, input, and framebuffer presentation through HostCompositor
   - Expected: simpleos_gui_adapter_display_path_name(adapter) equals `simpleos-framebuffer`
   - Expected: simpleos_gui_adapter_content_renderer_name(adapter) equals `simple_web`
   - Expected: adapter.delivered_bridge_events equals `1`
   - Expected: adapter.presented_frames equals `1`
   - Expected: adapter.compositor.windows.len() equals `1`
   - Expected: adapter.compositor.windows[0].content equals `adapter-ready`
   - Expected: _adapter_present_count equals `1`
   - Expected: _adapter_clear_color equals `0xFF0F172Au32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes bridge, input, and framebuffer presentation through HostCompositor")
_adapter_present_count = 0
_adapter_chrome_fill_count = 0
_adapter_clear_color = 0u32
val backend = AdapterCaptureBackend(w: 240, h: 180)
val adapter = SimpleOsGuiAdapter.new(backend, Size.wh(240, 180))

adapter.deliver_bridge_request(1, 44, COMP_CREATE_WINDOW.to_i64(), 0, "Terminal", 24, 36, 128, 92, "adapter-ready", 800, "/sys/apps/terminal")
# Pin the direct-draw chrome path: on Metal-capable hosts render_frame
# otherwise routes chrome via the CSS fast lane (blit + present only)
# and the per-element clear/fill counters this it asserts never fire.
host_wm_force_direct_chrome(true)
adapter.render_framebuffer_frame()
host_wm_force_direct_chrome(false)

expect(simpleos_gui_adapter_display_path_name(adapter)).to_equal("simpleos-framebuffer")
expect(simpleos_gui_adapter_content_renderer_name(adapter)).to_equal("simple_web")
expect(adapter.delivered_bridge_events).to_equal(1)
expect(adapter.presented_frames).to_equal(1)
expect(adapter.compositor.windows.len()).to_equal(1)
expect(adapter.compositor.windows[0].content).to_equal("adapter-ready")
expect(_adapter_present_count).to_equal(1)
expect(_adapter_chrome_fill_count).to_be_greater_than(0)
expect(_adapter_clear_color).to_equal(0xFF0F172Au32)
```

</details>

#### applies bridge lifecycle actions through the shared host compositor path

- applies bridge lifecycle actions through the shared host compositor path
   - Expected: adapter.compositor.windows[0].x equals `48`
   - Expected: adapter.compositor.windows[0].y equals `52`
   - Expected: adapter.compositor.windows[0].w equals `144`
   - Expected: adapter.compositor.windows[0].h equals `104`
   - Expected: adapter.compositor.windows[0].minimized is true
   - Expected: adapter.compositor.windows[0].minimized is false
   - Expected: adapter.compositor.windows[0].focused is true
   - Expected: adapter.delivered_bridge_events equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies bridge lifecycle actions through the shared host compositor path")
val backend = AdapterCaptureBackend(w: 240, h: 180)
val adapter = SimpleOsGuiAdapter.new(backend, Size.wh(240, 180))

adapter.deliver_bridge_request(1, 44, COMP_CREATE_WINDOW.to_i64(), 0, "Terminal", 24, 36, 128, 92, "adapter-ready", 800, "/sys/apps/terminal")
val wid = adapter.compositor.windows[0].id

adapter.deliver_bridge_request(2, 44, COMP_MOVE.to_i64(), wid, "", 48, 52, 0, 0, "", 0, "/sys/apps/terminal")
adapter.deliver_bridge_request(3, 44, COMP_RESIZE.to_i64(), wid, "", 0, 0, 144, 104, "", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows[0].x).to_equal(48)
expect(adapter.compositor.windows[0].y).to_equal(52)
expect(adapter.compositor.windows[0].w).to_equal(144)
expect(adapter.compositor.windows[0].h).to_equal(104)

adapter.deliver_bridge_request(4, 44, COMP_MINIMIZE.to_i64(), wid, "", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows[0].minimized).to_equal(true)

adapter.deliver_bridge_request(5, 44, COMP_RESTORE.to_i64(), wid, "", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows[0].minimized).to_equal(false)
expect(adapter.compositor.windows[0].focused).to_equal(true)
expect(adapter.delivered_bridge_events).to_equal(5)
```

</details>

#### applies title focus maximize update and destroy through the adapter bridge

- applies title focus maximize update and destroy through the adapter bridge
   - Expected: adapter.compositor.windows[0].title equals `Terminal Renamed`
   - Expected: adapter.compositor.windows[1].id equals `first_id`
   - Expected: adapter.compositor.windows[1].focused is true
   - Expected: adapter.compositor.windows[0].id equals `second_id`
   - Expected: adapter.compositor.windows[0].focused is false
   - Expected: adapter.compositor.windows[1].x equals `0`
   - Expected: adapter.compositor.windows[1].y equals `48`
   - Expected: adapter.compositor.windows[1].w equals `320`
   - Expected: adapter.compositor.windows[1].h equals `144`
   - Expected: adapter.compositor.windows[1].content equals `updated-content`
   - Expected: adapter.compositor.windows.len() equals `1`
   - Expected: adapter.compositor.windows[0].id equals `second_id`
   - Expected: adapter.delivered_bridge_events equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies title focus maximize update and destroy through the adapter bridge")
val backend = AdapterCaptureBackend(w: 320, h: 240)
val adapter = SimpleOsGuiAdapter.new(backend, Size.wh(320, 240))

adapter.deliver_bridge_request(1, 44, COMP_CREATE_WINDOW.to_i64(), 0, "Terminal", 24, 36, 128, 92, "adapter-ready", 800, "/sys/apps/terminal")
adapter.deliver_bridge_request(2, 55, COMP_CREATE_WINDOW.to_i64(), 0, "Editor", 64, 76, 150, 120, "editor-ready", 801, "/sys/apps/editor")
val first_id = adapter.compositor.windows[0].id
val second_id = adapter.compositor.windows[1].id

adapter.deliver_bridge_request(3, 44, COMP_SET_TITLE.to_i64(), first_id, "Terminal Renamed", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows[0].title).to_equal("Terminal Renamed")

adapter.deliver_bridge_request(4, 44, COMP_FOCUS.to_i64(), first_id, "", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows[1].id).to_equal(first_id)
expect(adapter.compositor.windows[1].focused).to_equal(true)
expect(adapter.compositor.windows[0].id).to_equal(second_id)
expect(adapter.compositor.windows[0].focused).to_equal(false)

adapter.deliver_bridge_request(5, 44, COMP_MAXIMIZE.to_i64(), first_id, "", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows[1].x).to_equal(0)
expect(adapter.compositor.windows[1].y).to_equal(48)
expect(adapter.compositor.windows[1].w).to_equal(320)
expect(adapter.compositor.windows[1].h).to_equal(144)

adapter.deliver_bridge_request(6, 44, COMP_UPDATE_TREE.to_i64(), first_id, "", 0, 0, 0, 0, "updated-content", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows[1].content).to_equal("updated-content")

adapter.deliver_bridge_request(7, 44, COMP_DESTROY_WINDOW.to_i64(), first_id, "", 0, 0, 0, 0, "", 0, "/sys/apps/terminal")
expect(adapter.compositor.windows.len()).to_equal(1)
expect(adapter.compositor.windows[0].id).to_equal(second_id)
expect(adapter.delivered_bridge_events).to_equal(7)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bae559c033079363ca2d492860042b57181234ea0b76471a919b2d4c10c5f4e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bae559c033079363ca2d492860042b57181234ea0b76471a919b2d4c10c5f4e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bae559c033079363ca2d492860042b57181234ea0b76471a919b2d4c10c5f4e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.spl
mirror: doc/06_spec/unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes bridge, input, and framebuffer presentation through HostCompositor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies bridge lifecycle actions through the shared host compositor path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/compositor/simpleos_gui_shared_wm_adapter_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies title focus maximize update and destroy through the adapter bridge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
