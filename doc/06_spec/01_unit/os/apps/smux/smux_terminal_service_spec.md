# smux_terminal_service_spec

> Behavioral specification for the smux terminal service: real child-process

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smux_terminal_service_spec

Behavioral specification for the smux terminal service: real child-process

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/smux/smux_terminal_service_spec.spl` |
| Updated | 2026-10-03 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Behavioral specification for the smux terminal service: real child-process
backing, authoritative focus, clock-sourced startup timing, typed errors for
unknown/cross-scope ids, survivor discoverability after a pane close, and
all-or-nothing admission.
Audience: IDE/terminal service maintainers.

## Scenarios

### smux terminal service

#### returns a nonce TRANSFORMED by the pane's child process

- Verify: a real child transforms what smux sends it
   - Expected: before.is_err() is true
   - Expected: spawned.is_ok() is true
   - Expected: smux_send_text(s.id, w.id, p.id, "nonce7f3a\n").is_ok() is true
   - Expected: seen equals `GOT:nonce7f3a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SMUX_TERMINAL_SERVICE-001
step("Verify: a real child transforms what smux sends it")
smux_reset_for_test()
val s = smux_create_session("pty")
val w = smux_list_windows(s.id)[0]
val p = smux_list_panes(s.id, w.id)[0]

# A pane with no child refuses input instead of appending to its buffer.
val before = smux_send_text(s.id, w.id, p.id, "nonce7f3a\n")
expect(before.is_err()).to_equal(true)

val spawned = smux_pane_spawn(s.id, w.id, p.id, "/bin/sh",
    ["-c", "while read l; do echo \"GOT:$l\"; done"])
expect(spawned.is_ok()).to_equal(true)

expect(smux_send_text(s.id, w.id, p.id, "nonce7f3a\n").is_ok()).to_equal(true)
val seen = _await_capture(s.id, w.id, p.id, "GOT:")
# The child upcases nothing but PREFIXES — an echo of the input alone
# would not contain "GOT:".
expect(seen).to_equal("GOT:nonce7f3a")
val _c = smux_close_pane(s.id, w.id, p.id)
```

</details>

#### focus mutates state so exactly one pane is focused and input routes there

- Verify: focus is authoritative, not a lookup that returns true
   - Expected: smux_focused_pane(s.id, w.id).unwrap().id equals `a.id`
   - Expected: smux_focus_pane(s.id, w.id, b.id) is true
   - Expected: smux_focused_pane(s.id, w.id).unwrap().id equals `b.id`
   - Expected: sp.is_ok() is true
   - Expected: smux_send_text(s.id, w.id, target.id, "routed\n").is_ok() is true
   - Expected: _await_capture(s.id, w.id, target.id, "B:") equals `B:routed`
   - Expected: smux_capture(s.id, w.id, a.id, 20).unwrap().content equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SMUX_TERMINAL_SERVICE-001
step("Verify: focus is authoritative, not a lookup that returns true")
smux_reset_for_test()
val s = smux_create_session("focus")
val w = smux_list_windows(s.id)[0]
val a = smux_list_panes(s.id, w.id)[0]
val b = smux_split_pane(s.id, w.id, a.id, "vertical").unwrap()

expect(smux_focused_pane(s.id, w.id).unwrap().id).to_equal(a.id)
expect(smux_focus_pane(s.id, w.id, b.id)).to_equal(true)
expect(smux_focused_pane(s.id, w.id).unwrap().id).to_equal(b.id)

# Input routed to the focused pane lands on B, and A never sees it.
val target = smux_focused_pane(s.id, w.id).unwrap()
val sp = smux_pane_spawn(s.id, w.id, target.id, "/bin/sh",
    ["-c", "while read l; do echo \"B:$l\"; done"])
expect(sp.is_ok()).to_equal(true)
expect(smux_send_text(s.id, w.id, target.id, "routed\n").is_ok()).to_equal(true)
expect(_await_capture(s.id, w.id, target.id, "B:")).to_equal("B:routed")
expect(smux_capture(s.id, w.id, a.id, 20).unwrap().content).to_equal("")
val _c = smux_close_pane(s.id, w.id, target.id)
```

</details>

#### window focus makes exactly one window active

- Verify: focusing a window deactivates its siblings
   - Expected: smux_active_window(s.id).unwrap().id equals `w0.id`
   - Expected: smux_focus_window(s.id, w1.id) is true
   - Expected: smux_active_window(s.id).unwrap().id equals `w1.id`
   - Expected: active equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SMUX_TERMINAL_SERVICE-001
step("Verify: focusing a window deactivates its siblings")
smux_reset_for_test()
val s = smux_create_session("wfocus")
val w0 = smux_list_windows(s.id)[0]
val w1 = smux_new_window(s.id, "build")
expect(smux_active_window(s.id).unwrap().id).to_equal(w0.id)
expect(smux_focus_window(s.id, w1.id)).to_equal(true)
expect(smux_active_window(s.id).unwrap().id).to_equal(w1.id)
var active = 0
val ws = smux_list_windows(s.id)
var i = 0
while i < ws.len():
    if ws[i].is_active:
        active = active + 1
    i = i + 1
expect(active).to_equal(1)
```

</details>

#### startup time comes from a clock and advances

- Verify: last_startup_ns is a real reading, not the literal 1
   - Expected: second >= first is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SMUX_TERMINAL_SERVICE-001
step("Verify: last_startup_ns is a real reading, not the literal 1")
smux_reset_for_test()
val _a = smux_create_session("t1")
val first = smux_metrics().last_startup_ns
expect(first).to_be_greater_than(1000000000000u64)
thread_sleep_ms(5)
val _b = smux_create_session("t2")
val second = smux_metrics().last_startup_ns
expect(second >= first).to_equal(true)
```

</details>

#### capture of an unknown pane is a typed error, not a fabricated row

- Verify: an unknown pane cannot masquerade as a one-row success
   - Expected: missing.is_err() is true
   - Expected: missing.unwrap_err() equals `unknown pane: no-such-pane`
   - Expected: smux_capture(s.id, w.id, p.id, 20).unwrap().rows equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SMUX_TERMINAL_SERVICE-001
step("Verify: an unknown pane cannot masquerade as a one-row success")
smux_reset_for_test()
val s = smux_create_session("cap")
val w = smux_list_windows(s.id)[0]
val missing = smux_capture(s.id, w.id, "no-such-pane", 20)
expect(missing.is_err()).to_equal(true)
expect(missing.unwrap_err()).to_equal("unknown pane: no-such-pane")
# An empty LIVE pane reports zero rows rather than a fabricated one.
val p = smux_list_panes(s.id, w.id)[0]
expect(smux_capture(s.id, w.id, p.id, 20).unwrap().rows).to_equal(0)
```

</details>

#### every survivor stays discoverable and writable after first/middle/last close

- Verify: pane removal compacts instead of orphaning later slots
   - Expected: smux_list_panes(s.id, w.id).len() equals `4`
   - Expected: smux_close_pane(s.id, w.id, p0.id) is true
   - Expected: smux_list_panes(s.id, w.id).len() equals `3`
   - Expected: smux_close_pane(s.id, w.id, p2.id) is true
   - Expected: smux_list_panes(s.id, w.id).len() equals `2`
   - Expected: smux_close_pane(s.id, w.id, p3.id) is true
   - Expected: left.len() equals `1`
   - Expected: left[0].id equals `p1.id`
   - Expected: smux_resize(s.id, w.id, p1.id, 100, 30).is_ok() is true
   - Expected: smux_capture(s.id, w.id, p1.id, 20).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SMUX_TERMINAL_SERVICE-001
step("Verify: pane removal compacts instead of orphaning later slots")
smux_reset_for_test()
val s = smux_create_session("close")
val w = smux_list_windows(s.id)[0]
val p0 = smux_list_panes(s.id, w.id)[0]
val p1 = smux_split_pane(s.id, w.id, p0.id, "v").unwrap()
val p2 = smux_split_pane(s.id, w.id, p0.id, "v").unwrap()
val p3 = smux_split_pane(s.id, w.id, p0.id, "v").unwrap()
expect(smux_list_panes(s.id, w.id).len()).to_equal(4)

# close FIRST
expect(smux_close_pane(s.id, w.id, p0.id)).to_equal(true)
expect(smux_list_panes(s.id, w.id).len()).to_equal(3)
# close MIDDLE (of the survivors)
expect(smux_close_pane(s.id, w.id, p2.id)).to_equal(true)
expect(smux_list_panes(s.id, w.id).len()).to_equal(2)
# close LAST
expect(smux_close_pane(s.id, w.id, p3.id)).to_equal(true)

val left = smux_list_panes(s.id, w.id)
expect(left.len()).to_equal(1)
expect(left[0].id).to_equal(p1.id)
# The survivor is still WRITABLE, not merely listed.
expect(smux_resize(s.id, w.id, p1.id, 100, 30).is_ok()).to_equal(true)
expect(smux_capture(s.id, w.id, p1.id, 20).is_ok()).to_equal(true)
```

</details>

#### rejects cross-session and cross-window id combinations

- Verify: every pane-addressed verb validates the whole triple
   - Expected: smux_focus_pane(a.id, wa.id, pb.id) is false
   - Expected: smux_close_pane(a.id, wa.id, pb.id) is false
   - Expected: smux_resize(a.id, wa.id, pb.id, 10, 10).is_err() is true
   - Expected: smux_capture(a.id, wa.id, pb.id, 5).is_err() is true
   - Expected: smux_send_text(a.id, wa.id, pb.id, "x").is_err() is true
   - Expected: smux_split_pane(a.id, wa.id, pb.id, "v").is_err() is true
   - Expected: smux_focus_pane(a.id, wb.id, pb.id) is false
   - Expected: smux_focus_window(a.id, wb.id) is false
   - Expected: smux_capture(b.id, wb.id, pa.id, 5).is_err() is true
   - Expected: smux_list_panes(a.id, wa.id).len() equals `1`
   - Expected: smux_list_panes(b.id, wb.id).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SMUX_TERMINAL_SERVICE-001
step("Verify: every pane-addressed verb validates the whole triple")
smux_reset_for_test()
val a = smux_create_session("A")
val wa = smux_list_windows(a.id)[0]
val pa = smux_list_panes(a.id, wa.id)[0]
val b = smux_create_session("B")
val wb = smux_list_windows(b.id)[0]
val pb = smux_list_panes(b.id, wb.id)[0]

# pane of B addressed with session/window of A
expect(smux_focus_pane(a.id, wa.id, pb.id)).to_equal(false)
expect(smux_close_pane(a.id, wa.id, pb.id)).to_equal(false)
expect(smux_resize(a.id, wa.id, pb.id, 10, 10).is_err()).to_equal(true)
expect(smux_capture(a.id, wa.id, pb.id, 5).is_err()).to_equal(true)
expect(smux_send_text(a.id, wa.id, pb.id, "x").is_err()).to_equal(true)
expect(smux_split_pane(a.id, wa.id, pb.id, "v").is_err()).to_equal(true)

# window of B addressed with session of A
expect(smux_focus_pane(a.id, wb.id, pb.id)).to_equal(false)
expect(smux_focus_window(a.id, wb.id)).to_equal(false)

# pane of A addressed with the window of B (which is in session B)
expect(smux_capture(b.id, wb.id, pa.id, 5).is_err()).to_equal(true)

# nothing above mutated anything
expect(smux_list_panes(a.id, wa.id).len()).to_equal(1)
expect(smux_list_panes(b.id, wb.id).len()).to_equal(1)
```

</details>

#### admission is all-or-nothing and never hands back a phantom id

- Verify: an over-capacity request creates nothing and refuses clearly
   - Expected: smux_list_sessions().len() equals `8`
   - Expected: smux_admission_available() is false
   - Expected: overflow.id equals ``
   - Expected: smux_list_sessions().len() equals `8`
   - Expected: smux_list_windows("").len() equals `0`
   - Expected: split.is_err() is true
   - Expected: smux_list_panes(s0.id, w0.id).len() equals `1`
   - Expected: smux_new_window(s0.id, "extra").id equals ``
   - Expected: smux_list_windows(s0.id).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SMUX_TERMINAL_SERVICE-001
step("Verify: an over-capacity request creates nothing and refuses clearly")
smux_reset_for_test()
var i = 0
while i < 8:
    val made = smux_create_session("s" + i.to_text())
    expect(made.id).to_not_equal("")
    i = i + 1
expect(smux_list_sessions().len()).to_equal(8)
expect(smux_admission_available()).to_equal(false)

val overflow = smux_create_session("s8")
expect(overflow.id).to_equal("")
# Nothing was created: no ninth session, and no orphan window or pane.
expect(smux_list_sessions().len()).to_equal(8)
expect(smux_list_windows("").len()).to_equal(0)

# A split that cannot be seated is a typed error, not Ok(phantom).
val s0 = smux_list_sessions()[0]
val w0 = smux_list_windows(s0.id)[0]
val p0 = smux_list_panes(s0.id, w0.id)[0]
val split = smux_split_pane(s0.id, w0.id, p0.id, "v")
expect(split.is_err()).to_equal(true)
expect(smux_list_panes(s0.id, w0.id).len()).to_equal(1)

# An over-capacity window request is refused with an empty id too.
expect(smux_new_window(s0.id, "extra").id).to_equal("")
expect(smux_list_windows(s0.id).len()).to_equal(1)
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
