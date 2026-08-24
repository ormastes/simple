# @manual: primary

> Purpose: Prove the smux native terminal multiplexer's system-level behavior —

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove the smux native terminal multiplexer's system-level behavior —

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/smux_system_spec.spl` |
| Updated | 2026-08-24 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove the smux native terminal multiplexer's system-level behavior —
session/window/pane persistence, attach/detach, split and resize, input/output
routing, capture, the tmux-shaped compatibility surface, deferred features, and
the observability counters.
Audience: engineers changing `src/os/apps/smux/**` who need to know which
operator-visible multiplexer behaviors are pinned before they touch the
service, api, or contract layers.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
These scenarios drive the smux service surface in interpreter mode with local
in-memory session tables; the real PTY allocation and on-screen renderer are
out of scope. Unit-level value-model coverage lives in
`test/01_unit/os/smux_spec.spl`.
# @manual: primary
REQ-TOOLS-SMUX-SYSTEM-001
doc/01_research/os/qemu/tmux_simpleos.md
doc/03_plan/sys_test/smux_caret_sspec_quality.md
doc/04_architecture/os/tmux_simpleos.md
doc/05_design/os/desktop/tmux_simpleos_tui.md

## Scenarios

### smux native terminal multiplexer system behaviour

### REQ-001 — persistent session/window/pane model

#### create session returns named session

- Exercise create session returns named session
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: s.name equals `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-001
step("Exercise create session returns named session")
_reset()
val s = _create_session("main")
expect(s.name).to_equal("main")
```

</details>

#### session has non-empty id

- Exercise session has non-empty id
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-001
step("Exercise session has non-empty id")
_reset()
val s = _create_session("alpha")
expect(s.id != "").to_be(true)
```

</details>

#### list sessions includes created session

- Exercise list sessions includes created session
   - TUI capture: after_step
   - Evidence: TUI state verified by 2 expected checks
   - Expected: list.len() equals `1`
   - Expected: list[0].id equals `s.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-001
step("Exercise list sessions includes created session")
_reset()
val s = _create_session("alpha")
val list = _list_sessions()
expect(list.len()).to_equal(1)  # oracle: exactly one session was created, so the session table holds one row
expect(list[0].id).to_equal(s.id)
```

</details>

#### session auto-creates window

- Exercise session auto-creates window
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: windows.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-001
step("Exercise session auto-creates window")
_reset()
val s = _create_session("boot")
val windows = _list_windows(s.id)
expect(windows.len()).to_equal(1)  # oracle: creating a session auto-creates exactly one window
```

</details>

#### session auto-creates pane

- Exercise session auto-creates pane
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: panes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-001
step("Exercise session auto-creates pane")
_reset()
val s = _create_session("boot")
val windows = _list_windows(s.id)
val panes = _list_panes(s.id, windows[0].id)
expect(panes.len()).to_equal(1)  # oracle: the auto-created window owns exactly one pane
```

</details>

#### multiple sessions all listed

- Exercise multiple sessions all listed
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: list.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-001
step("Exercise multiple sessions all listed")
_reset()
val _s1 = _create_session("s1")
val _s2 = _create_session("s2")
val list = _list_sessions()
expect(list.len()).to_equal(2)  # oracle: both created sessions remain listed
```

</details>

#### new_window adds window

- Exercise new_window adds window
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: windows.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-001
step("Exercise new_window adds window")
_reset()
val s = _create_session("ws")
val _w2 = _new_window(s.id, "editor")
val windows = _list_windows(s.id)
expect(windows.len()).to_equal(2)  # oracle: the auto-created window plus the explicitly added one
```

</details>

#### new_window auto-creates pane

- Exercise new_window auto-creates pane
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: panes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-001
step("Exercise new_window auto-creates pane")
_reset()
val s = _create_session("wp")
val w2 = _new_window(s.id, "term")
val panes = _list_panes(s.id, w2.id)
expect(panes.len()).to_equal(1)  # oracle: a newly added window auto-creates exactly one pane
```

</details>

### REQ-002 — pane-backed shell execution

#### initial pane state is running

- Exercise initial pane state is running
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: panes[0].state equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-002
step("Exercise initial pane state is running")
_reset()
val s = _create_session("sh")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
expect(panes[0].state).to_equal("running")
```

</details>

#### initial pane has non-zero dimensions

- Exercise initial pane has non-zero dimensions
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-002
step("Exercise initial pane has non-zero dimensions")
_reset()
val s = _create_session("dim")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val p = panes[0]
expect(p.cols > 0).to_be(true)
expect(p.rows > 0).to_be(true)
```

</details>

### REQ-003 — attach/detach without session destruction

#### attach registers client against session

- Exercise attach registers client against session
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: att.session_id equals `s.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-003
step("Exercise attach registers client against session")
_reset()
val s = _create_session("adet")
val att = _attach(s.id, "client-1", 80, 24)
expect(att.attached).to_be(true)
expect(att.session_id).to_equal(s.id)
```

</details>

#### detach returns true

- Exercise detach returns true
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-003
step("Exercise detach returns true")
_reset()
val s = _create_session("det")
val _att = _attach(s.id, "client-2", 80, 24)
val ok = _detach("client-2")
expect(ok).to_be(true)
```

</details>

#### session persists after detach

- Exercise session persists after detach
   - TUI capture: after_step
   - Evidence: TUI state verified by 2 expected checks
   - Expected: list.len() equals `1`
   - Expected: list[0].id equals `s.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-003
step("Exercise session persists after detach")
_reset()
val s = _create_session("persist")
val _att = _attach(s.id, "client-3", 80, 24)
val _d = _detach("client-3")
val list = _list_sessions()
expect(list.len()).to_equal(1)  # oracle: detach must not destroy the session, so one session remains
expect(list[0].id).to_equal(s.id)
```

</details>

#### detach unknown client returns false

- Exercise detach unknown client returns false
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-003
step("Exercise detach unknown client returns false")
_reset()
val ok = _detach("ghost-client")
expect(ok).to_equal(false)
```

</details>

#### reattach after detach succeeds

- Exercise reattach after detach succeeds
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-003
step("Exercise reattach after detach succeeds")
_reset()
val s = _create_session("reatt")
val _a1 = _attach(s.id, "client-4", 80, 24)
val _d = _detach("client-4")
val a2 = _attach(s.id, "client-4", 80, 24)
expect(a2.attached).to_be(true)
```

</details>

### REQ-004 — split/layout operations

#### split vertical creates pane

- Exercise split vertical creates pane
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-004
step("Exercise split vertical creates pane")
_reset()
val s = _create_session("split")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val ok = _split_pane(s.id, wins[0].id, panes[0].id, "vertical")
expect(ok).to_be(true)
```

</details>

#### split horizontal creates pane

- Exercise split horizontal creates pane
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-004
step("Exercise split horizontal creates pane")
_reset()
val s = _create_session("splith")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val ok = _split_pane(s.id, wins[0].id, panes[0].id, "horizontal")
expect(ok).to_be(true)
```

</details>

#### split invalid pane returns false

- Exercise split invalid pane returns false
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-004
step("Exercise split invalid pane returns false")
_reset()
val s = _create_session("spliterr")
val wins = _list_windows(s.id)
val ok = _split_pane(s.id, wins[0].id, "bad-pane-id", "vertical")
expect(ok).to_equal(false)
```

</details>

#### resize pane returns true

- Exercise resize pane returns true
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-004
step("Exercise resize pane returns true")
_reset()
val s = _create_session("resize")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val ok = _resize_pane(panes[0].id, 120, 40)
expect(ok).to_be(true)
```

</details>

#### resize invalid pane returns false

- Exercise resize invalid pane returns false
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-004
step("Exercise resize invalid pane returns false")
_reset()
val ok = _resize_pane("no-such-pane", 100, 30)
expect(ok).to_equal(false)
```

</details>

### REQ-005 — input/output routing

#### send_command to valid pane succeeds

- Exercise send_command to valid pane succeeds
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-005
step("Exercise send_command to valid pane succeeds")
_reset()
val s = _create_session("io")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val ok = _send_command(panes[0].id, "echo hello")
expect(ok).to_be(true)
```

</details>

#### send_command to invalid pane returns false

- Exercise send_command to invalid pane returns false
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-005
step("Exercise send_command to invalid pane returns false")
_reset()
val ok = _send_command("bad-pane", "echo hi")
expect(ok).to_equal(false)
```

</details>

#### capture has correct pane identity after send

- Exercise capture has correct pane identity after send
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: cap.pane_id equals `pid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-005
step("Exercise capture has correct pane identity after send")
_reset()
val s = _create_session("iosend")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val pid = panes[0].id
val _sent = _send_command(pid, "hello world")
val cap = _capture(pid)
expect(cap.pane_id).to_equal(pid)
```

</details>

### REQ-006 — state query API

#### list_sessions returns stable metadata

- Exercise list_sessions returns stable metadata
   - TUI capture: after_step
   - Evidence: TUI state verified by 2 expected checks
   - Expected: l1.len() equals `l2.len()`
   - Expected: l1[0].id equals `l2[0].id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-006
step("Exercise list_sessions returns stable metadata")
_reset()
val s = _create_session("stable")
val l1 = _list_sessions()
val l2 = _list_sessions()
expect(l1.len()).to_equal(l2.len())
expect(l1[0].id).to_equal(l2[0].id)
```

</details>

#### list_windows returns stable metadata

- Exercise list_windows returns stable metadata
   - TUI capture: after_step
   - Evidence: TUI state verified by 2 expected checks
   - Expected: w1.len() equals `w2.len()`
   - Expected: w1[0].id equals `w2[0].id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-006
step("Exercise list_windows returns stable metadata")
_reset()
val s = _create_session("wstable")
val w1 = _list_windows(s.id)
val w2 = _list_windows(s.id)
expect(w1.len()).to_equal(w2.len())
expect(w1[0].id).to_equal(w2[0].id)
```

</details>

#### list_panes returns stable metadata

- Exercise list_panes returns stable metadata
   - TUI capture: after_step
   - Evidence: TUI state verified by 2 expected checks
   - Expected: p1.len() equals `p2.len()`
   - Expected: p1[0].id equals `p2[0].id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-006
step("Exercise list_panes returns stable metadata")
_reset()
val s = _create_session("pstable")
val wins = _list_windows(s.id)
val p1 = _list_panes(s.id, wins[0].id)
val p2 = _list_panes(s.id, wins[0].id)
expect(p1.len()).to_equal(p2.len())
expect(p1[0].id).to_equal(p2[0].id)
```

</details>

#### pane metadata includes session and window ids

- Exercise pane metadata includes session and window ids
   - TUI capture: after_step
   - Evidence: TUI state verified by 2 expected checks
   - Expected: p.session_id equals `s.id`
   - Expected: p.window_id equals `wins[0].id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-006
step("Exercise pane metadata includes session and window ids")
_reset()
val s = _create_session("pmeta")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val p = panes[0]
expect(p.session_id).to_equal(s.id)
expect(p.window_id).to_equal(wins[0].id)
```

</details>

### REQ-007 — capture API

#### capture returns valid pane identity

- Exercise capture returns valid pane identity
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: cap.pane_id equals `pid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-007
step("Exercise capture returns valid pane identity")
_reset()
val s = _create_session("cap")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val pid = panes[0].id
val cap = _capture(pid)
expect(cap.pane_id).to_equal(pid)
```

</details>

#### capture rows is greater than zero

- Exercise capture rows is greater than zero
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-007
step("Exercise capture rows is greater than zero")
_reset()
val s = _create_session("caprows")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val cap = _capture(panes[0].id)
expect(cap.rows > 0).to_be(true)
```

</details>

#### capture increments capture_count

- Exercise capture increments capture_count
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: after equals `before + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-007
step("Exercise capture increments capture_count")
_reset()
val s = _create_session("capmet")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val pid = panes[0].id
val before = _get_metrics().capture_count
val _c = _capture(pid)
val after = _get_metrics().capture_count
expect(after).to_equal(before + 1)
```

</details>

#### capture on unknown pane returns minimal non-crash result

- Exercise capture on unknown pane returns minimal non-crash result
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-007
step("Exercise capture on unknown pane returns minimal non-crash result")
_reset()
val cap = _capture("no-pane")
expect(cap.rows > 0).to_be(true)
```

</details>

### REQ-008 — compatibility-facing tmux-shaped API

#### MuxSession has id and name fields

- Exercise MuxSession has id and name fields
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: s.name equals `compat`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-008
step("Exercise MuxSession has id and name fields")
_reset()
val s = _create_session("compat")
expect(s.id != "").to_be(true)
expect(s.name).to_equal("compat")
```

</details>

#### MuxWindow has id and session_id

- Exercise MuxWindow has id and session_id
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: wins[0].session_id equals `s.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-008
step("Exercise MuxWindow has id and session_id")
_reset()
val s = _create_session("cw")
val wins = _list_windows(s.id)
expect(wins[0].id != "").to_be(true)
expect(wins[0].session_id).to_equal(s.id)
```

</details>

#### MuxPane has id, window_id, session_id

- Exercise MuxPane has id, window_id, session_id
   - TUI capture: after_step
   - Evidence: TUI state verified by 2 expected checks
   - Expected: p.window_id equals `wins[0].id`
   - Expected: p.session_id equals `s.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-008
step("Exercise MuxPane has id, window_id, session_id")
_reset()
val s = _create_session("cp")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val p = panes[0]
expect(p.id != "").to_be(true)
expect(p.window_id).to_equal(wins[0].id)
expect(p.session_id).to_equal(s.id)
```

</details>

#### MuxCapture has non-empty pane_id

- Exercise MuxCapture has non-empty pane_id
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-008
step("Exercise MuxCapture has non-empty pane_id")
_reset()
val s = _create_session("cc")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val cap = _capture(panes[0].id)
expect(cap.pane_id != "").to_be(true)
```

</details>

#### MuxSession to_text returns non-empty

- Exercise MuxSession to_text returns non-empty
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-008
step("Exercise MuxSession to_text returns non-empty")
_reset()
val s = _create_session("tt")
val t = s.to_text()
expect(t != "").to_be(true)
```

</details>

### REQ-009 — native-first backend, no upstream tmux dependency

#### backend contract name is smux-native

- Exercise backend contract name is smux-native
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: name equals `smux-native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-009
step("Exercise backend contract name is smux-native")
val name = _backend_name()
expect(name).to_equal("smux-native")
```

</details>

#### service operates without host tmux

- Exercise service operates without host tmux
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: panes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-009
step("Exercise service operates without host tmux")
_reset()
val s = _create_session("natv")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
expect(panes.len()).to_equal(1)  # oracle: the native backend auto-creates one pane with no host tmux present
```

</details>

### REQ-010 — backend swap readiness boundary

#### backend contract name queryable independently of adapter surface

- Exercise backend contract name queryable independently of adapter surface
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-010
step("Exercise backend contract name queryable independently of adapter surface")
val name = _backend_name()
expect(name != "").to_be(true)
```

</details>

#### pane has non-empty to_text representation

- Exercise pane has non-empty to_text representation
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-010
step("Exercise pane has non-empty to_text representation")
_reset()
val s = _create_session("bkswap")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val t = panes[0].to_text()
expect(t != "").to_be(true)
```

</details>

### REQ-011 — explicit non-fatal failure handling

#### split invalid pane returns false not crash

- Exercise split invalid pane returns false not crash
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-011
step("Exercise split invalid pane returns false not crash")
_reset()
val s = _create_session("err1")
val wins = _list_windows(s.id)
val ok = _split_pane(s.id, wins[0].id, "ghost", "vertical")
expect(ok).to_equal(false)
```

</details>

#### resize invalid pane returns false not crash

- Exercise resize invalid pane returns false not crash
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-011
step("Exercise resize invalid pane returns false not crash")
_reset()
val ok = _resize_pane("ghost", 80, 24)
expect(ok).to_equal(false)
```

</details>

#### send_command invalid pane returns false not crash

- Exercise send_command invalid pane returns false not crash
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-011
step("Exercise send_command invalid pane returns false not crash")
_reset()
val ok = _send_command("ghost", "ls")
expect(ok).to_equal(false)
```

</details>

#### detach unknown client returns false not crash

- Exercise detach unknown client returns false not crash
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-011
step("Exercise detach unknown client returns false not crash")
_reset()
val ok = _detach("nobody")
expect(ok).to_equal(false)
```

</details>

#### capture unknown pane returns minimal result not crash

- Exercise capture unknown pane returns minimal result not crash
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-011
step("Exercise capture unknown pane returns minimal result not crash")
_reset()
val cap = _capture("nowhere")
expect(cap.rows > 0).to_be(true)
```

</details>

### REQ-012 — declared deferrals remain deferred and are queryable

#### copy-mode is deferred

- Exercise copy-mode is deferred
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-012
step("Exercise copy-mode is deferred")
expect(_is_deferred("copy-mode")).to_be(true)
```

</details>

#### mouse is deferred

- Exercise mouse is deferred
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-012
step("Exercise mouse is deferred")
expect(_is_deferred("mouse")).to_be(true)
```

</details>

#### key-table-compat is deferred

- Exercise key-table-compat is deferred
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-012
step("Exercise key-table-compat is deferred")
expect(_is_deferred("key-table-compat")).to_be(true)
```

</details>

#### tmux-conf is deferred

- Exercise tmux-conf is deferred
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-012
step("Exercise tmux-conf is deferred")
expect(_is_deferred("tmux-conf")).to_be(true)
```

</details>

#### control-mode is deferred

- Exercise control-mode is deferred
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-012
step("Exercise control-mode is deferred")
expect(_is_deferred("control-mode")).to_be(true)
```

</details>

#### non-deferred feature returns false

- Exercise non-deferred feature returns false
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: _is_deferred("session-create") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, REQ-012
step("Exercise non-deferred feature returns false")
expect(_is_deferred("session-create")).to_equal(false)
```

</details>

### NFR-007 — startup/operation observability counters

#### startup_count increments with each session

- Exercise startup_count increments with each session
   - TUI capture: after_step
   - Evidence: TUI state verified by 3 expected checks
   - Expected: _get_metrics().startup_count equals `0`
   - Expected: _get_metrics().startup_count equals `1`
   - Expected: _get_metrics().startup_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, NFR-007
step("Exercise startup_count increments with each session")
_reset()
expect(_get_metrics().startup_count).to_equal(0)  # oracle: a reset service reports a zeroed startup counter
val _s1 = _create_session("obs1")
expect(_get_metrics().startup_count).to_equal(1)  # oracle: one session has been created since reset
val _s2 = _create_session("obs2")
expect(_get_metrics().startup_count).to_equal(2)  # oracle: two sessions have been created since reset
```

</details>

#### capture_count increments with each capture

- Exercise capture_count increments with each capture
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: _get_metrics().capture_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, NFR-007
step("Exercise capture_count increments with each capture")
_reset()
val s = _create_session("obscap")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val pid = panes[0].id
val _c1 = _capture(pid)
val _c2 = _capture(pid)
expect(_get_metrics().capture_count).to_equal(2)  # oracle: two capture calls were issued against the pane
```

</details>

#### resize_count increments with each resize

- Exercise resize_count increments with each resize
   - TUI capture: after_step
   - Evidence: TUI state verified by 1 expected check
   - Expected: _get_metrics().resize_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, NFR-007
step("Exercise resize_count increments with each resize")
_reset()
val s = _create_session("obsrez")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val _r = _resize_pane(panes[0].id, 100, 30)
expect(_get_metrics().resize_count).to_equal(1)  # oracle: one resize call was issued against the pane
```

</details>

#### metrics are zero after reset

- Exercise metrics are zero after reset
   - TUI capture: after_step
   - Evidence: TUI state verified by 3 expected checks
   - Expected: _get_metrics().startup_count equals `0`
   - Expected: _get_metrics().capture_count equals `0`
   - Expected: _get_metrics().resize_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, NFR-007
step("Exercise metrics are zero after reset")
_reset()
expect(_get_metrics().startup_count).to_equal(0)  # oracle: reset zeroes the startup counter
expect(_get_metrics().capture_count).to_equal(0)  # oracle: reset zeroes the capture counter
expect(_get_metrics().resize_count).to_equal(0)  # oracle: reset zeroes the resize counter
```

</details>

#### all metric counters are non-negative

- Exercise all metric counters are non-negative
   - TUI capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-TOOLS-SMUX-SYSTEM-001, NFR-007
step("Exercise all metric counters are non-negative")
_reset()
val _s = _create_session("mneg")
expect(_get_metrics().startup_count >= 0).to_be(true)
expect(_get_metrics().capture_count >= 0).to_be(true)
expect(_get_metrics().resize_count >= 0).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-TOOLS-SMUX-SYSTEM-001`
- `REQ-001`
- `REQ-012`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
- `REQ-009`
- `REQ-010`
- `REQ-011`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0c455bcac532c6af8b55f143a6ce358ae128cbd94cb1a33d6c171760be11b0b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0c455bcac532c6af8b55f143a6ce358ae128cbd94cb1a33d6c171760be11b0b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0c455bcac532c6af8b55f143a6ce358ae128cbd94cb1a33d6c171760be11b0b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/tools/smux_system_spec.spl
mirror: doc/06_spec/03_system/tools/smux_system_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/smux_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/smux_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
