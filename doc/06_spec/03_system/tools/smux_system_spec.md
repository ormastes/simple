# @manual: primary

> Purpose: Prove that smux system.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that smux system.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/smux_system_spec.spl` |
| Updated | 2026-08-24 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that smux system.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-TOOLS-SMUX-SYSTEM-001
doc/01_research/tools/REQ-TOOLS-SMUX-SYSTEM-001.md
doc/03_plan/tools/REQ-TOOLS-SMUX-SYSTEM-001.md
doc/04_architecture/tools/REQ-TOOLS-SMUX-SYSTEM-001.md
doc/05_design/tools/REQ-TOOLS-SMUX-SYSTEM-001.md

## Scenarios

### smux native terminal multiplexer system behaviour

### REQ-001 — persistent session/window/pane model

#### should create session returns named session

- Exercise create session returns named session
   - Expected: s.name equals `main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise create session returns named session")
_reset()
val s = _create_session("main")
expect(s.name).to_equal("main")
```

</details>

#### should session has non-empty id

- Exercise session has non-empty id


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise session has non-empty id")
_reset()
val s = _create_session("alpha")
expect(s.id != "").to_be(true)
```

</details>

#### should list sessions includes created session

- Exercise list sessions includes created session
   - Expected: list.len() equals `1`
   - Expected: list[0].id equals `s.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise list sessions includes created session")
_reset()
val s = _create_session("alpha")
val list = _list_sessions()
expect(list.len()).to_equal(1)
expect(list[0].id).to_equal(s.id)
```

</details>

#### should session auto-creates window

- Exercise session auto-creates window
   - Expected: windows.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise session auto-creates window")
_reset()
val s = _create_session("boot")
val windows = _list_windows(s.id)
expect(windows.len()).to_equal(1)
```

</details>

#### should session auto-creates pane

- Exercise session auto-creates pane
   - Expected: panes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise session auto-creates pane")
_reset()
val s = _create_session("boot")
val windows = _list_windows(s.id)
val panes = _list_panes(s.id, windows[0].id)
expect(panes.len()).to_equal(1)
```

</details>

#### should multiple sessions all listed

- Exercise multiple sessions all listed
   - Expected: list.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise multiple sessions all listed")
_reset()
val _s1 = _create_session("s1")
val _s2 = _create_session("s2")
val list = _list_sessions()
expect(list.len()).to_equal(2)
```

</details>

#### should new_window adds window

- Exercise new_window adds window
   - Expected: windows.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise new_window adds window")
_reset()
val s = _create_session("ws")
val _w2 = _new_window(s.id, "editor")
val windows = _list_windows(s.id)
expect(windows.len()).to_equal(2)
```

</details>

#### should new_window auto-creates pane

- Exercise new_window auto-creates pane
   - Expected: panes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise new_window auto-creates pane")
_reset()
val s = _create_session("wp")
val w2 = _new_window(s.id, "term")
val panes = _list_panes(s.id, w2.id)
expect(panes.len()).to_equal(1)
```

</details>

### REQ-002 — pane-backed shell execution

#### should initial pane state is running

- Exercise initial pane state is running
   - Expected: panes[0].state equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise initial pane state is running")
_reset()
val s = _create_session("sh")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
expect(panes[0].state).to_equal("running")
```

</details>

#### should initial pane has non-zero dimensions

- Exercise initial pane has non-zero dimensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### should attach registers client against session

- Exercise attach registers client against session
   - Expected: att.session_id equals `s.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise attach registers client against session")
_reset()
val s = _create_session("adet")
val att = _attach(s.id, "client-1", 80, 24)
expect(att.attached).to_be(true)
expect(att.session_id).to_equal(s.id)
```

</details>

#### should detach returns true

- Exercise detach returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise detach returns true")
_reset()
val s = _create_session("det")
val _att = _attach(s.id, "client-2", 80, 24)
val ok = _detach("client-2")
expect(ok).to_be(true)
```

</details>

#### should session persists after detach

- Exercise session persists after detach
   - Expected: list.len() equals `1`
   - Expected: list[0].id equals `s.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise session persists after detach")
_reset()
val s = _create_session("persist")
val _att = _attach(s.id, "client-3", 80, 24)
val _d = _detach("client-3")
val list = _list_sessions()
expect(list.len()).to_equal(1)
expect(list[0].id).to_equal(s.id)
```

</details>

#### should detach unknown client returns false

- Exercise detach unknown client returns false
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise detach unknown client returns false")
_reset()
val ok = _detach("ghost-client")
expect(ok).to_equal(false)
```

</details>

#### should reattach after detach succeeds

- Exercise reattach after detach succeeds


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### should split vertical creates pane

- Exercise split vertical creates pane


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise split vertical creates pane")
_reset()
val s = _create_session("split")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val ok = _split_pane(s.id, wins[0].id, panes[0].id, "vertical")
expect(ok).to_be(true)
```

</details>

#### should split horizontal creates pane

- Exercise split horizontal creates pane


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise split horizontal creates pane")
_reset()
val s = _create_session("splith")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val ok = _split_pane(s.id, wins[0].id, panes[0].id, "horizontal")
expect(ok).to_be(true)
```

</details>

#### should split invalid pane returns false

- Exercise split invalid pane returns false
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise split invalid pane returns false")
_reset()
val s = _create_session("spliterr")
val wins = _list_windows(s.id)
val ok = _split_pane(s.id, wins[0].id, "bad-pane-id", "vertical")
expect(ok).to_equal(false)
```

</details>

#### should resize pane returns true

- Exercise resize pane returns true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise resize pane returns true")
_reset()
val s = _create_session("resize")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val ok = _resize_pane(panes[0].id, 120, 40)
expect(ok).to_be(true)
```

</details>

#### should resize invalid pane returns false

- Exercise resize invalid pane returns false
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise resize invalid pane returns false")
_reset()
val ok = _resize_pane("no-such-pane", 100, 30)
expect(ok).to_equal(false)
```

</details>

### REQ-005 — input/output routing

#### should send_command to valid pane succeeds

- Exercise send_command to valid pane succeeds


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise send_command to valid pane succeeds")
_reset()
val s = _create_session("io")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val ok = _send_command(panes[0].id, "echo hello")
expect(ok).to_be(true)
```

</details>

#### should send_command to invalid pane returns false

- Exercise send_command to invalid pane returns false
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise send_command to invalid pane returns false")
_reset()
val ok = _send_command("bad-pane", "echo hi")
expect(ok).to_equal(false)
```

</details>

#### should capture has correct pane identity after send

- Exercise capture has correct pane identity after send
   - Expected: cap.pane_id equals `pid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### should list_sessions returns stable metadata

- Exercise list_sessions returns stable metadata
   - Expected: l1.len() equals `l2.len()`
   - Expected: l1[0].id equals `l2[0].id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise list_sessions returns stable metadata")
_reset()
val s = _create_session("stable")
val l1 = _list_sessions()
val l2 = _list_sessions()
expect(l1.len()).to_equal(l2.len())
expect(l1[0].id).to_equal(l2[0].id)
```

</details>

#### should list_windows returns stable metadata

- Exercise list_windows returns stable metadata
   - Expected: w1.len() equals `w2.len()`
   - Expected: w1[0].id equals `w2[0].id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise list_windows returns stable metadata")
_reset()
val s = _create_session("wstable")
val w1 = _list_windows(s.id)
val w2 = _list_windows(s.id)
expect(w1.len()).to_equal(w2.len())
expect(w1[0].id).to_equal(w2[0].id)
```

</details>

#### should list_panes returns stable metadata

- Exercise list_panes returns stable metadata
   - Expected: p1.len() equals `p2.len()`
   - Expected: p1[0].id equals `p2[0].id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### should pane metadata includes session and window ids

- Exercise pane metadata includes session and window ids
   - Expected: p.session_id equals `s.id`
   - Expected: p.window_id equals `wins[0].id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### should capture returns valid pane identity

- Exercise capture returns valid pane identity
   - Expected: cap.pane_id equals `pid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### should capture rows is greater than zero

- Exercise capture rows is greater than zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise capture rows is greater than zero")
_reset()
val s = _create_session("caprows")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val cap = _capture(panes[0].id)
expect(cap.rows > 0).to_be(true)
```

</details>

#### should capture increments capture_count

- Exercise capture increments capture_count
   - Expected: after equals `before + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### should capture on unknown pane returns minimal non-crash result

- Exercise capture on unknown pane returns minimal non-crash result


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise capture on unknown pane returns minimal non-crash result")
_reset()
val cap = _capture("no-pane")
expect(cap.rows > 0).to_be(true)
```

</details>

### REQ-008 — compatibility-facing tmux-shaped API

#### should MuxSession has id and name fields

- Exercise MuxSession has id and name fields
   - Expected: s.name equals `compat`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise MuxSession has id and name fields")
_reset()
val s = _create_session("compat")
expect(s.id != "").to_be(true)
expect(s.name).to_equal("compat")
```

</details>

#### should MuxWindow has id and session_id

- Exercise MuxWindow has id and session_id
   - Expected: wins[0].session_id equals `s.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise MuxWindow has id and session_id")
_reset()
val s = _create_session("cw")
val wins = _list_windows(s.id)
expect(wins[0].id != "").to_be(true)
expect(wins[0].session_id).to_equal(s.id)
```

</details>

#### should MuxPane has id, window_id, session_id

- Exercise MuxPane has id, window_id, session_id
   - Expected: p.window_id equals `wins[0].id`
   - Expected: p.session_id equals `s.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### should MuxCapture has non-empty pane_id

- Exercise MuxCapture has non-empty pane_id


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise MuxCapture has non-empty pane_id")
_reset()
val s = _create_session("cc")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val cap = _capture(panes[0].id)
expect(cap.pane_id != "").to_be(true)
```

</details>

#### should MuxSession to_text returns non-empty

- Exercise MuxSession to_text returns non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise MuxSession to_text returns non-empty")
_reset()
val s = _create_session("tt")
val t = s.to_text()
expect(t != "").to_be(true)
```

</details>

### REQ-009 — native-first backend, no upstream tmux dependency

#### should backend contract name is smux-native

- Exercise backend contract name is smux-native
   - Expected: name equals `smux-native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise backend contract name is smux-native")
val name = _backend_name()
expect(name).to_equal("smux-native")
```

</details>

#### should service operates without host tmux

- Exercise service operates without host tmux
   - Expected: panes.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise service operates without host tmux")
_reset()
val s = _create_session("natv")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
expect(panes.len()).to_equal(1)
```

</details>

### REQ-010 — backend swap readiness boundary

#### should backend contract name queryable independently of adapter surface

- Exercise backend contract name queryable independently of adapter surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise backend contract name queryable independently of adapter surface")
val name = _backend_name()
expect(name != "").to_be(true)
```

</details>

#### should pane has non-empty to_text representation

- Exercise pane has non-empty to_text representation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### should split invalid pane returns false not crash

- Exercise split invalid pane returns false not crash
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise split invalid pane returns false not crash")
_reset()
val s = _create_session("err1")
val wins = _list_windows(s.id)
val ok = _split_pane(s.id, wins[0].id, "ghost", "vertical")
expect(ok).to_equal(false)
```

</details>

#### should resize invalid pane returns false not crash

- Exercise resize invalid pane returns false not crash
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise resize invalid pane returns false not crash")
_reset()
val ok = _resize_pane("ghost", 80, 24)
expect(ok).to_equal(false)
```

</details>

#### should send_command invalid pane returns false not crash

- Exercise send_command invalid pane returns false not crash
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise send_command invalid pane returns false not crash")
_reset()
val ok = _send_command("ghost", "ls")
expect(ok).to_equal(false)
```

</details>

#### should detach unknown client returns false not crash

- Exercise detach unknown client returns false not crash
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise detach unknown client returns false not crash")
_reset()
val ok = _detach("nobody")
expect(ok).to_equal(false)
```

</details>

#### should capture unknown pane returns minimal result not crash

- Exercise capture unknown pane returns minimal result not crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise capture unknown pane returns minimal result not crash")
_reset()
val cap = _capture("nowhere")
expect(cap.rows > 0).to_be(true)
```

</details>

### REQ-012 — declared deferrals remain deferred and are queryable

#### should copy-mode is deferred

- Exercise copy-mode is deferred


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise copy-mode is deferred")
expect(_is_deferred("copy-mode")).to_be(true)
```

</details>

#### should mouse is deferred

- Exercise mouse is deferred


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise mouse is deferred")
expect(_is_deferred("mouse")).to_be(true)
```

</details>

#### should key-table-compat is deferred

- Exercise key-table-compat is deferred


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise key-table-compat is deferred")
expect(_is_deferred("key-table-compat")).to_be(true)
```

</details>

#### should tmux-conf is deferred

- Exercise tmux-conf is deferred


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise tmux-conf is deferred")
expect(_is_deferred("tmux-conf")).to_be(true)
```

</details>

#### should control-mode is deferred

- Exercise control-mode is deferred


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise control-mode is deferred")
expect(_is_deferred("control-mode")).to_be(true)
```

</details>

#### should non-deferred feature returns false

- Exercise non-deferred feature returns false
   - Expected: _is_deferred("session-create") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise non-deferred feature returns false")
expect(_is_deferred("session-create")).to_equal(false)
```

</details>

### NFR-007 — startup/operation observability counters

#### should startup_count increments with each session

- Exercise startup_count increments with each session
   - Expected: _get_metrics().startup_count equals `0`
   - Expected: _get_metrics().startup_count equals `1`
   - Expected: _get_metrics().startup_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise startup_count increments with each session")
_reset()
expect(_get_metrics().startup_count).to_equal(0)
val _s1 = _create_session("obs1")
expect(_get_metrics().startup_count).to_equal(1)
val _s2 = _create_session("obs2")
expect(_get_metrics().startup_count).to_equal(2)
```

</details>

#### should capture_count increments with each capture

- Exercise capture_count increments with each capture
   - Expected: _get_metrics().capture_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise capture_count increments with each capture")
_reset()
val s = _create_session("obscap")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val pid = panes[0].id
val _c1 = _capture(pid)
val _c2 = _capture(pid)
expect(_get_metrics().capture_count).to_equal(2)
```

</details>

#### should resize_count increments with each resize

- Exercise resize_count increments with each resize
   - Expected: _get_metrics().resize_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise resize_count increments with each resize")
_reset()
val s = _create_session("obsrez")
val wins = _list_windows(s.id)
val panes = _list_panes(s.id, wins[0].id)
val _r = _resize_pane(panes[0].id, 100, 30)
expect(_get_metrics().resize_count).to_equal(1)
```

</details>

#### should metrics are zero after reset

- Exercise metrics are zero after reset
   - Expected: _get_metrics().startup_count equals `0`
   - Expected: _get_metrics().capture_count equals `0`
   - Expected: _get_metrics().resize_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise metrics are zero after reset")
_reset()
expect(_get_metrics().startup_count).to_equal(0)
expect(_get_metrics().capture_count).to_equal(0)
expect(_get_metrics().resize_count).to_equal(0)
```

</details>

#### should all metric counters are non-negative

- Exercise all metric counters are non-negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5ca70ad5f7af16d3b844e9100d00fbca77bd48eacac929ea45fb9f582fc5fcc1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5ca70ad5f7af16d3b844e9100d00fbca77bd48eacac929ea45fb9f582fc5fcc1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5ca70ad5f7af16d3b844e9100d00fbca77bd48eacac929ea45fb9f582fc5fcc1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **71/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/tools/smux_system_spec.spl
mirror: doc/06_spec/03_system/tools/smux_system_spec.md (current)
findings: 15 blockers: 1
  narrative=100 structure=70 oracle=70
  traceability=60 evidence=40 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=71; blocker cap makes effective=49
doc/06_spec/03_system/tools/smux_system_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/tools/smux_system_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/03_system/tools/smux_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/smux_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/smux_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/smux_system_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 12 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/tools/smux_system_spec.spl:217:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create session returns named session' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/smux_system_spec.spl:217:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create session returns named session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/smux_system_spec.spl:224:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should session has non-empty id' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/smux_system_spec.spl:224:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should session has non-empty id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/smux_system_spec.spl:231:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should list sessions includes created session' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/smux_system_spec.spl:231:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should list sessions includes created session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/smux_system_spec.spl:240:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should session auto-creates window' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/smux_system_spec.spl:248:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should session auto-creates pane' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/smux_system_spec.spl:257:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should multiple sessions all listed' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
