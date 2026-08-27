# Shell Baremetal Backend Specification

> Tests covering baremetal shared WM backend contract, SimpleOS authoritative render revisions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shell Baremetal Backend Specification

## Scenarios

### baremetal shared WM backend contract

#### renders a live SharedWmScene instead of synthesizing overlay windows

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders a live SharedWmScene instead of synthesizing overlay windows
   - Expected: backend.clear_count equals `1`
   - Expected: backend.present_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("renders a live SharedWmScene instead of synthesizing overlay windows")
var backend = _capture_backend()
val window = simple_gui_internal_window(
    "surface-41", "41", 7001u64, "editor", "Live Editor",
    80, 70, 420, 300, "document=notes.spl", false, true, 0
)
val scene = simple_gui_internal_window_scene(800, 600, "simpleos-compositor", [window])

val pixels = _solid_pixels(412 * 264, 0xFF102030u32)
val frame = WmContentFrame(window_id: "41", scene_revision: 7, content_revision: 3, origin_kind: WM_CONTENT_ORIGIN_SIMPLE_WEB, width: 412, height: 264, pixels: pixels, checksum: wm_content_frame_checksum(pixels), parent_window_id: "", offset_x: 0, offset_y: 0)
render_baremetal_shared_wm_scene(backend, scene, empty_taskbar_model(), [frame], 7, 9, "12:34")

expect(backend.clear_count).to_equal(1)
expect(backend.fill_count > 0).to_be(true)
expect(backend.text_count > 0).to_be(true)
expect(backend.present_count).to_equal(0)
```

</details>

<details>
<summary>Advanced: routes the production loop through authoritative runtime scene inputs</summary>

#### routes the production loop through authoritative runtime scene inputs

- routes the production loop through authoritative runtime scene inputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("routes the production loop through authoritative runtime scene inputs")
val src = file_read("src/os/desktop/shell.spl")
# index_of returns a raw i64 (-1 when absent), never nil. Assert the
# opening marker exists rather than slicing from -1, and fall back to
# end-of-file when the closing marker is absent — `?? src.len()` never
# fired on that miss.
val run_start = src.index_of("me run_baremetal")
expect(run_start).to_be_greater_than(-1)
var snapshot_start = src.index_of("fn runtime_scene_snapshot")
if snapshot_start < 0:
    snapshot_start = src.len()
expect(snapshot_start).to_be_greater_than(run_start)
val run_body = src.slice(run_start, snapshot_start)
expect(src).to_contain("me render_baremetal_frame(executor: Engine2dWmFrameExecutor)")
expect(src).to_contain("executor.render(scene, taskbar, content_frames")
expect(run_body).to_contain("self.render_baremetal_frame(executor)")
expect(run_body.contains("render_baremetal_shared_wm_scene")).to_be(false)
```

</details>


</details>

#### routes the live taskbar model and clock through shared taskbar object rendering

- routes the live taskbar model and clock through shared taskbar object rendering


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("routes the live taskbar model and clock through shared taskbar object rendering")
val src = file_read("src/os/desktop/shell_baremetal.spl")
expect(src).to_contain("shared_wm_scene_render_taskbar_context_to_backend")
expect(src).to_contain("SharedWmTaskbarRenderInput")
expect(src.contains("shared_wm_scene_render_to_backend_with_taskbar")).to_be(false)
```

</details>

### SimpleOS authoritative render revisions

#### keeps unchanged state stable and covers title app content and focus mutations

- keeps unchanged state stable and covers title app content and focus mutations
   - Expected: shell.runtime_scene_revision() equals `stable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps unchanged state stable and covers title app content and focus mutations")
var compositor = Compositor.with_backends(_capture_backend(), nil, 800, 600)
val first = compositor.create_window("Editor", 40, 60, 320, 240)
val second = compositor.create_window("Terminal", 90, 100, 300, 220)
compositor.set_window_identity(first, 71, "editor")
compositor.update_window_content(first.to_u64(), "<main>one</main>")
var shell = DesktopShell.new(compositor)

val stable = shell.runtime_scene_revision()
expect(shell.runtime_scene_revision()).to_equal(stable)

shell.compositor.set_window_title(first.to_u64(), "Notes")
val title_revision = shell.runtime_scene_revision()
expect(title_revision == stable).to_be(false)

shell.compositor.set_window_identity(first, 71, "notes")
val app_revision = shell.runtime_scene_revision()
expect(app_revision == title_revision).to_be(false)

shell.compositor.update_window_content(first.to_u64(), "<main>two</main>")
val content_revision = shell.runtime_scene_revision()
expect(content_revision == app_revision).to_be(false)

shell.compositor.focus_window(first)
expect(shell.runtime_scene_revision() == content_revision).to_be(false)
```

</details>

#### keeps taskbar revision stable and changes it for clock title app and minimized state

- keeps taskbar revision stable and changes it for clock title app and minimized state
   - Expected: shell.runtime_taskbar_revision() equals `stable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps taskbar revision stable and changes it for clock title app and minimized state")
var compositor = Compositor.with_backends(_capture_backend(), nil, 800, 600)
val id = compositor.create_window("Editor", 40, 60, 320, 240)
compositor.set_window_identity(id, 71, "editor")
var shell = DesktopShell.new(compositor)

val stable = shell.runtime_taskbar_revision()
expect(shell.runtime_taskbar_revision()).to_equal(stable)
shell.clock_text = "12:35"
val clock_revision = shell.runtime_taskbar_revision()
expect(clock_revision == stable).to_be(false)
shell.compositor.set_window_title(id.to_u64(), "Notes")
val title_revision = shell.runtime_taskbar_revision()
expect(title_revision == clock_revision).to_be(false)
shell.compositor.set_window_identity(id, 71, "notes")
val app_revision = shell.runtime_taskbar_revision()
expect(app_revision == title_revision).to_be(false)
shell.compositor.minimize_window(id.to_u64())
expect(shell.runtime_taskbar_revision() == app_revision).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/shell_baremetal_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering baremetal shared WM backend contract, SimpleOS authoritative render revisions.
- baremetal shared WM backend contract
- SimpleOS authoritative render revisions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a90fd961234f2cbbb181c58fdb73ec457877f41f284d8287815e71b84a6f96e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a90fd961234f2cbbb181c58fdb73ec457877f41f284d8287815e71b84a6f96e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a90fd961234f2cbbb181c58fdb73ec457877f41f284d8287815e71b84a6f96e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/desktop/shell_baremetal_backend_spec.spl
mirror: doc/06_spec/01_unit/os/desktop/shell_baremetal_backend_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/desktop/shell_baremetal_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/desktop/shell_baremetal_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/desktop/shell_baremetal_backend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/desktop/shell_baremetal_backend_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes the production loop through authoritative runtime scene inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/desktop/shell_baremetal_backend_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes the live taskbar model and clock through shared taskbar object rendering' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
