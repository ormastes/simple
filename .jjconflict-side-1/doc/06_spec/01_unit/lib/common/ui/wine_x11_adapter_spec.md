# Wine X11 Adapter Specification

> Tests covering Wine X11-class backend adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine X11 Adapter Specification

## Scenarios

### Wine X11-class backend adapter

#### starts with only display and screen discovery

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts with only display and screen discovery
   - Expected: wine_x11_backend_feature_gate(backend) equals `missing-window`
   - Expected: wine_x11_backend_event_state(backend) equals `missing-create`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("starts with only display and screen discovery")
val backend = wine_x11_backend_new()
expect(wine_x11_backend_feature_gate(backend)).to_equal("missing-window")
expect(wine_x11_backend_event_state(backend)).to_equal("missing-create")
```

</details>

#### creates, maps, configures, focuses, and unmaps windows

- creates, maps, configures, focuses, and unmaps windows
   - Expected: created.state equals `created`
   - Expected: focused.backend.focused_window equals `w1`
   - Expected: unmapped.backend.focused_window equals ``
   - Expected: wine_x11_backend_event_state(focused.backend) equals `missing-unmap`
   - Expected: wine_x11_backend_event_state(unmapped.backend) equals `missing-expose`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates, maps, configures, focuses, and unmaps windows")
val created = wine_x11_create_window(wine_x11_backend_new(), "w1")
expect(created.state).to_equal("created")
val mapped = wine_x11_map_window(created.backend, "w1")
val configured = wine_x11_configure_window(mapped.backend, "w1", 800, 600)
val focused = wine_x11_focus_window(configured.backend, "w1")
val unmapped = wine_x11_unmap_window(focused.backend, "w1")
expect(focused.backend.focused_window).to_equal("w1")
expect(unmapped.backend.focused_window).to_equal("")
expect(wine_x11_backend_event_state(focused.backend)).to_equal("missing-unmap")
expect(wine_x11_backend_event_state(unmapped.backend)).to_equal("missing-expose")
```

</details>

#### rejects operations on missing windows

- rejects operations on missing windows
   - Expected: damaged.ok is false
   - Expected: damaged.state equals `missing-window`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects operations on missing windows")
val damaged = wine_x11_damage_window(wine_x11_backend_new(), "missing")
expect(damaged.ok).to_equal(false)
expect(damaged.state).to_equal("missing-window")
```

</details>

#### records damage, present, text, glyph, fill, and cursor pixel evidence

- records damage, present, text, glyph, fill, and cursor pixel evidence
   - Expected: wine_x11_backend_pixel_state(cursor.backend) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records damage, present, text, glyph, fill, and cursor pixel evidence")
val created = wine_x11_create_window(wine_x11_backend_new(), "w1")
val mapped = wine_x11_map_window(created.backend, "w1")
val damaged = wine_x11_damage_window(mapped.backend, "w1")
val filled = wine_x11_fill_window(damaged.backend, "w1")
val texted = wine_x11_text_window(filled.backend, "w1", "abc")
val cursor = wine_x11_set_cursor(texted.backend, "ibeam")
expect(cursor.backend.features).to_contain("glyph")
expect(wine_x11_backend_pixel_state(cursor.backend)).to_equal("ready")
```

</details>

#### records clipboard and destroy events

- records clipboard and destroy events
   - Expected: destroyed.backend.clipboard_text equals `hello`
   - Expected: destroyed.backend.mapped_windows.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records clipboard and destroy events")
val created = wine_x11_create_window(wine_x11_backend_new(), "w1")
val clip = wine_x11_set_clipboard(created.backend, "hello")
val destroyed = wine_x11_destroy_window(clip.backend, "w1")
expect(destroyed.backend.clipboard_text).to_equal("hello")
expect(destroyed.backend.mapped_windows.len()).to_equal(0)
```

</details>

#### records X11 WM atom and property evidence for Wine windows

- records X11 WM atom and property evidence for Wine windows
   - Expected: wine_x11_backend_property_state(stated.backend) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("records X11 WM atom and property evidence for Wine windows")
val created = wine_x11_create_window(wine_x11_backend_new(), "w1")
val atom = wine_x11_intern_atom(created.backend, "WM_DELETE_WINDOW")
val named = wine_x11_set_wm_name(atom.backend, "w1", "hello")
val classed = wine_x11_set_wm_class(named.backend, "w1", "hello.exe", "Wine")
val protocols = wine_x11_set_wm_protocols(classed.backend, "w1", ["WM_DELETE_WINDOW"])
val stated = wine_x11_set_wm_state(protocols.backend, "w1", "_NET_WM_STATE_NORMAL")
expect(stated.backend.features).to_contain("wm-protocols")
expect(stated.backend.properties).to_contain("WM_DELETE_WINDOW")
expect(wine_x11_backend_property_state(stated.backend)).to_equal("ready")
```

</details>

#### rejects invalid X11 WM property operations

- rejects invalid X11 WM property operations
   - Expected: empty_atom.ok is false
   - Expected: empty_atom.state equals `invalid-atom`
   - Expected: missing_window.ok is false
   - Expected: missing_window.state equals `missing-window`
   - Expected: empty_protocols.ok is false
   - Expected: empty_protocols.state equals `invalid-property`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid X11 WM property operations")
val created = wine_x11_create_window(wine_x11_backend_new(), "w1")
val empty_atom = wine_x11_intern_atom(created.backend, "")
expect(empty_atom.ok).to_equal(false)
expect(empty_atom.state).to_equal("invalid-atom")
val missing_window = wine_x11_set_wm_name(created.backend, "missing", "hello")
expect(missing_window.ok).to_equal(false)
expect(missing_window.state).to_equal("missing-window")
val empty_protocols = wine_x11_set_wm_protocols(created.backend, "w1", [])
expect(empty_protocols.ok).to_equal(false)
expect(empty_protocols.state).to_equal("invalid-property")
```

</details>

#### polls deterministic X11-class events in FIFO order

- polls deterministic X11-class events in FIFO order
   - Expected: configured.backend.event_queue.len() equals `3`
   - Expected: first.event equals `create:w1`
   - Expected: second.event equals `map:w1`
   - Expected: third.event equals `configure:w1`
   - Expected: empty.state equals `event-queue-empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("polls deterministic X11-class events in FIFO order")
val created = wine_x11_create_window(wine_x11_backend_new(), "w1")
val mapped = wine_x11_map_window(created.backend, "w1")
val configured = wine_x11_configure_window(mapped.backend, "w1", 800, 600)
val first = wine_x11_poll_event(configured.backend)
val second = wine_x11_poll_event(first.backend)
val third = wine_x11_poll_event(second.backend)
val empty = wine_x11_poll_event(third.backend)
expect(configured.backend.event_queue.len()).to_equal(3)
expect(first.event).to_equal("create:w1")
expect(second.event).to_equal("map:w1")
expect(third.event).to_equal("configure:w1")
expect(empty.state).to_equal("event-queue-empty")
```

</details>

#### reaches the existing X11-class feature, event, and pixel gates

- reaches the existing X11-class feature, event, and pixel gates
   - Expected: result.ok is true
   - Expected: wine_x11_backend_feature_gate(result.backend) equals `ready`
   - Expected: wine_x11_backend_event_state(result.backend) equals `ready`
   - Expected: wine_x11_backend_pixel_state(result.backend) equals `ready`
   - Expected: wine_x11_backend_property_state(result.backend) equals `ready`
   - Expected: wine_x11_backend_ready(result.backend) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reaches the existing X11-class feature, event, and pixel gates")
val result = _ready_backend()
expect(result.ok).to_equal(true)
expect(wine_x11_backend_feature_gate(result.backend)).to_equal("ready")
expect(wine_x11_backend_event_state(result.backend)).to_equal("ready")
expect(wine_x11_backend_pixel_state(result.backend)).to_equal("ready")
expect(wine_x11_backend_property_state(result.backend)).to_equal("ready")
expect(wine_x11_backend_ready(result.backend)).to_equal("ready")
```

</details>

#### does not treat modeled X11 readiness as production readiness

- does not treat modeled X11 readiness as production readiness
   - Expected: wine_x11_backend_ready(result.backend) equals `ready`
   - Expected: wine_x11_backend_production_ready(result.backend) equals `missing-simpleos-window-record`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not treat modeled X11 readiness as production readiness")
val result = _ready_backend()
expect(wine_x11_backend_ready(result.backend)).to_equal("ready")
expect(wine_x11_backend_production_ready(result.backend)).to_equal("missing-simpleos-window-record")
```

</details>

#### binds SimpleOS window evidence for production readiness

- binds SimpleOS window evidence for production readiness
   - Expected: bound.ok is true
   - Expected: wine_x11_backend_production_ready(bound.backend) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("binds SimpleOS window evidence for production readiness")
val result = _ready_backend()
val created = wine_simpleos_create_window(wine_simpleos_window_bridge_new(), 1, "wine", "hello", 640, 480)
val mapped = wine_simpleos_map_window(created.bridge, 1)
val configured = wine_simpleos_configure_window(mapped.bridge, 1, 0, 0, 640, 480)
val focused = wine_simpleos_focus_window(configured.bridge, 1)
val presented = wine_simpleos_present_window(focused.bridge, 1, 3)
val cursor = wine_simpleos_set_cursor(presented.bridge, "arrow")
val clipboard = wine_simpleos_set_clipboard(cursor.bridge, "clip")
val unmapped = wine_simpleos_unmap_window(clipboard.bridge, 1)
val destroyed = wine_simpleos_destroy_window(unmapped.bridge, 1)
val bound = wine_x11_backend_bind_simpleos(result.backend, destroyed.bridge)
expect(bound.ok).to_equal(true)
expect(wine_x11_backend_production_ready(bound.backend)).to_equal("ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/wine_x11_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine X11-class backend adapter.
- Wine X11-class backend adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `96304b8e269e8c4a2600185e6dbff822788a7a3d385168476f0fc2e927019392`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `96304b8e269e8c4a2600185e6dbff822788a7a3d385168476f0fc2e927019392`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `96304b8e269e8c4a2600185e6dbff822788a7a3d385168476f0fc2e927019392`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/ui/wine_x11_adapter_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/wine_x11_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/wine_x11_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/wine_x11_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/wine_x11_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/wine_x11_adapter_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with only display and screen discovery' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/wine_x11_adapter_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates, maps, configures, focuses, and unmaps windows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/wine_x11_adapter_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects operations on missing windows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
