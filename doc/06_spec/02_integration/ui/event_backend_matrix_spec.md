# event_backend_matrix_spec

> Purpose: This spec proves host platform event backend detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# event_backend_matrix_spec

Purpose: This spec proves host platform event backend detection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/ui/event_backend_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves host platform event backend detection.
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### host platform event backend detection

#### returns a valid EventBackend variant

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns a valid EventBackend variant


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-EVENTBACKENDMATRIX-001
step("returns a valid EventBackend variant")
val name = _backend_name_of(detect_backend())
val valid = name == "epoll" or name == "kqueue" or name == "iocp" or name == "event_port" or name == "poll"
assert_true(valid)
```

</details>

#### matches the running OS exactly (Epoll on this Linux host)

- matches the running OS exactly (Epoll on this Linux host)
- matches the running OS exactly (Epoll on this Linux host)
   - Expected: name equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("matches the running OS exactly (Epoll on this Linux host)")
step("matches the running OS exactly (Epoll on this Linux host)")
# Conditional on the module's own os gate (rt_platform_name), NOT a
# weakened assert: on the Linux CI host the "linux" branch runs and
# pins Epoll exactly; every other platform pins its own exact
# backend per the documented contract in platform_event.spl.
val platform = rt_platform_name()
var expected = "poll"
if platform == "linux":
    expected = "epoll"
else if platform == "macos" or platform == "freebsd":
    expected = "kqueue"
else if platform == "windows":
    expected = "iocp"
else if platform == "solaris" or platform == "illumos":
    expected = "event_port"
val name = _backend_name_of(detect_backend())
expect(name).to_equal(expected)
```

</details>

#### PlatformEvent.new() adopts the detected backend

- PlatformEvent.new() adopts the detected backend
- PlatformEvent.new() adopts the detected backend
   - Expected: pe.backend_name() equals `_backend_name_of(detect_backend())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("PlatformEvent.new() adopts the detected backend")
step("PlatformEvent.new() adopts the detected backend")
val pe = PlatformEvent.new()
expect(pe.backend_name()).to_equal(_backend_name_of(detect_backend()))
```

</details>

### EventLoop smoke on the native backend

#### creates, polls non-blocking with no fds, and closes cleanly

- creates, polls non-blocking with no fds, and closes cleanly
- creates, polls non-blocking with no fds, and closes cleanly
   - Expected: _event_loop_smoke_mask() equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates, polls non-blocking with no fds, and closes cleanly")
step("creates, polls non-blocking with no fds, and closes cleanly")
# All 5 stages — see _event_loop_smoke_mask's comment for the bit map
# and the interp-shim regression this gates.
expect(_event_loop_smoke_mask()).to_equal(31)
```

</details>

### interaction backend composition

#### composes hit_stack, capture/target/bubble dispatch, and pointer-capture redirect

- composes hit_stack, capture/target/bubble dispatch, and pointer-capture redirect
- composes hit_stack, capture/target/bubble dispatch, and pointer-capture
   - Expected: hit.primary equals `3`
   - Expected: hit.ancestor_path.len() equals `3`
   - Expected: hit.ancestor_path[0] equals `1`
   - Expected: hit.ancestor_path[1] equals `2`
   - Expected: hit.ancestor_path[2] equals `3`
   - Expected: outcome.fired_node_ids.len() equals `5`
   - Expected: outcome.fired_node_ids[0] equals `1)   # capture: root`
   - Expected: outcome.fired_node_ids[1] equals `2)   # capture: mid`
   - Expected: outcome.fired_node_ids[2] equals `3)   # target`
   - Expected: outcome.fired_node_ids[3] equals `2)   # bubble: mid`
   - Expected: outcome.fired_node_ids[4] equals `1)   # bubble: root`
   - Expected: outcome.stopped is false
   - Expected: outcome.default_prevented is false
   - Expected: hit_outside.primary equals `-1`
   - Expected: effective_target(router, 7, hit_outside) equals `2`
   - Expected: redirected_path.len() equals `2`
   - Expected: redirected_path[0] equals `1`
   - Expected: redirected_path[1] equals `2`
   - Expected: effective_target(router, 7, hit_outside) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("composes hit_stack, capture/target/bubble dispatch, and pointer-capture redirect")
step("composes hit_stack, capture/target/bubble dispatch, and pointer-capture ")
# Three nested rects: root(1) > mid(2) > inner(3); inner paints on
# top via tree_order (same stacking context / layer / z).
val proxies = [
    _proxy(1, 0, 0, 100, 100, 0),
    _proxy(2, 10, 10, 90, 90, 1),
    _proxy(3, 20, 20, 80, 80, 2)
]
var parents: Dict<i64, i64> = {}
parents[2] = 1
parents[3] = 2

# Hit inside the innermost rect resolves the root-to-target path.
val hit = hit_stack(proxies, parents, 50, 50)
expect(hit.primary).to_equal(3)
expect(hit.ancestor_path.len()).to_equal(3)
expect(hit.ancestor_path[0]).to_equal(1)
expect(hit.ancestor_path[1]).to_equal(2)
expect(hit.ancestor_path[2]).to_equal(3)

# POINTER_DOWN through capture -> target -> bubble. Handlers RETURN
# action masks (never mutate the event from inside a callback — the
# documented cross-module landmine); dispatch itself records the
# visit order in the returned DispatchOutcome.
val listeners = [
    EventListener2D.create(1, -1, true, false, _handler_none),
    EventListener2D.create(2, -1, true, false, _handler_none),
    EventListener2D.create(3, -1, false, false, _handler_none),
    EventListener2D.create(2, -1, false, false, _handler_none),
    EventListener2D.create(1, -1, false, false, _handler_none)
]
val event = PointerEvent2D.create(7, POINTER_DOWN, 50, 50, 1, hit.primary)
val outcome = dispatch(event, listeners, hit.ancestor_path)
expect(outcome.fired_node_ids.len()).to_equal(5)
expect(outcome.fired_node_ids[0]).to_equal(1)   # capture: root
expect(outcome.fired_node_ids[1]).to_equal(2)   # capture: mid
expect(outcome.fired_node_ids[2]).to_equal(3)   # target
expect(outcome.fired_node_ids[3]).to_equal(2)   # bubble: mid
expect(outcome.fired_node_ids[4]).to_equal(1)   # bubble: root
expect(outcome.stopped).to_equal(false)
expect(outcome.default_prevented).to_equal(false)

# Capture pointer 7 on the mid ancestor: a point OUTSIDE every proxy
# must keep routing to node 2 until release, with the redirected
# ancestor path rebuilt via ancestor_path_of (not hit.ancestor_path).
var router = PointerRouter.create()
router.capture_pointer(7, 2)
val hit_outside = hit_stack(proxies, parents, 500, 500)
expect(hit_outside.primary).to_equal(-1)
expect(effective_target(router, 7, hit_outside)).to_equal(2)
val redirected_path = ancestor_path_of(parents, 2)
expect(redirected_path.len()).to_equal(2)
expect(redirected_path[0]).to_equal(1)
expect(redirected_path[1]).to_equal(2)
router.release_pointer(7)
expect(effective_target(router, 7, hit_outside)).to_equal(-1)
```

</details>

### window event backends on a headless host

#### pins the winit event type codes against drift

- pins the winit event type codes against drift
- pins the winit event type codes against drift
   - Expected: EVT_CLOSE equals `3`
   - Expected: EVT_KEYBOARD equals `10`
   - Expected: EVT_MOUSE_BUTTON equals `20`
   - Expected: EVT_MOUSE_MOVED equals `21`
   - Expected: EVT_MOUSE_WHEEL equals `22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pins the winit event type codes against drift")
step("pins the winit event type codes against drift")
# Constants only — no window, no event loop thread. See the header
# note for why no availability probe is exercised (and the SDL2
# named-constant gap).
expect(EVT_CLOSE).to_equal(3)
expect(EVT_KEYBOARD).to_equal(10)
expect(EVT_MOUSE_BUTTON).to_equal(20)
expect(EVT_MOUSE_MOVED).to_equal(21)
expect(EVT_MOUSE_WHEEL).to_equal(22)
```

</details>

### UISession event path smoke

#### processes a synthetic keypress through the pure reducer

- processes a synthetic keypress through the pure reducer
- processes a synthetic keypress through the pure reducer
   - Expected: s0.mode_name() equals `NORMAL`
   - Expected: s1.mode_name() equals `INSERT`
   - Expected: s2.mode_name() equals `NORMAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("processes a synthetic keypress through the pure reducer")
step("processes a synthetic keypress through the pure reducer")
val root = text_widget("evt_matrix_root", "Events")
val tree = UITree.new(root)
var s0 = UIState.new(tree)
expect(s0.mode_name()).to_equal("NORMAL")
var s1 = process_event(s0, UIEvent.KeyPress(key: "i"))
expect(s1.mode_name()).to_equal("INSERT")
var s2 = process_event(s1, UIEvent.NormalMode)
expect(s2.mode_name()).to_equal("NORMAL")
```

</details>

#### routes a synthetic keypress through a live session

- routes a synthetic keypress through a live session
- routes a synthetic keypress through a live session
   - Expected: before.mode_name() equals `NORMAL`
   - Expected: after.mode_name() equals `INSERT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("routes a synthetic keypress through a live session")
step("routes a synthetic keypress through a live session")
val root = text_widget("evt_matrix_sess_root", "Session")
val tree = UITree.new(root)
var session = new_session(tree)
var before = session.current_state()
expect(before.mode_name()).to_equal("NORMAL")
session.dispatch(UIEvent.KeyPress(key: "i"))
var after = session.current_state()
expect(after.mode_name()).to_equal("INSERT")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-EVENTBACKENDMATRIX-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f9493cfc2d2705e2c5e55b8e6bfb704db81504a5f61cc21f00689392ac05ad35`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f9493cfc2d2705e2c5e55b8e6bfb704db81504a5f61cc21f00689392ac05ad35`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f9493cfc2d2705e2c5e55b8e6bfb704db81504a5f61cc21f00689392ac05ad35`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/ui/event_backend_matrix_spec.spl
mirror: doc/06_spec/02_integration/ui/event_backend_matrix_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/ui/event_backend_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/ui/event_backend_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/ui/event_backend_matrix_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/ui/event_backend_matrix_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a valid EventBackend variant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/ui/event_backend_matrix_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the running OS exactly (Epoll on this Linux host)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/ui/event_backend_matrix_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PlatformEvent.new() adopts the detected backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
