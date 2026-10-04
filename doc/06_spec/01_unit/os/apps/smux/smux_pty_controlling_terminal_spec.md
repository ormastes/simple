# smux_pty_controlling_terminal_spec

> Behavioral specification for the smux PTY lane: a pane spawned with

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smux_pty_controlling_terminal_spec

Behavioral specification for the smux PTY lane: a pane spawned with

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/smux/smux_pty_controlling_terminal_spec.spl` |
| Updated | 2026-10-03 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Behavioral specification for the smux PTY lane: a pane spawned with
`smux_pane_spawn_pty` gives its child a REAL controlling terminal, while the
default pipe lane does not.

The oracle is deliberately NOT "the extern returned something". It is a
contrast: the SAME command is run through both lanes, and the expected outputs
cannot be produced by an echo of the input.

  POSIX    `tty`       PTY -> a device path under /dev/    pipe -> "not a tty"
  POSIX    `stty size` PTY -> the pane's own rows/cols     pipe -> not a terminal
  Windows  `mode con`  ConPTY -> the pane's own Lines/Columns
                       pipe   -> the host console the test runner inherited

Audience: IDE/terminal service maintainers.

## Scenarios

### smux PTY lane gives a pane a controlling terminal

#### a PTY-backed child sees its own terminal; the same command on a pipe does not

- Verify: the PTY child's terminal is the pane, the piped child's is not
   - Expected: smux_resize(sa.id, wa.id, pa.id, 97, 31).is_ok() is true
   - Expected: spawned.is_ok() is true
   - Expected: smux_pane_is_pty(sa.id, wa.id, pa.id).unwrap() is true
   - Expected: smux_send_text(sa.id, wa.id, pa.id, "mode con\r").is_ok() is true
   - Expected: smux_send_text(sa.id, wa.id, pa.id, "tty\n").is_ok() is true
   - Expected: pty_seen contains `/dev/`
   - Expected: pty_seen does not contain `not a tty`
   - Expected: smux_resize(sb.id, wb.id, pb.id, 97, 31).is_ok() is true
   - Expected: smux_pane_is_pty(sb.id, wb.id, pb.id).unwrap() is false
   - Expected: smux_pane_spawn(sb.id, wb.id, pb.id, "cmd.exe", ["/q", "/k"]).is_ok() is true
   - Expected: smux_send_text(sb.id, wb.id, pb.id, "mode con\r\n").is_ok() is true
   - Expected: pipe_seen does not contain `Columns: 97`
   - Expected: smux_pane_spawn(sb.id, wb.id, pb.id, "/bin/sh", []).is_ok() is true
   - Expected: smux_send_text(sb.id, wb.id, pb.id, "tty\n").is_ok() is true
   - Expected: pipe_seen contains `not a tty`
   - Expected: pipe_seen does not contain `/dev/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SMUX_PTY_CONTROLLING_TERMINAL-001
step("Verify: the PTY child's terminal is the pane, the piped child's is not")
smux_reset_for_test()

# --- A. PTY lane ---
val sa = smux_create_session("ptylane")
val wa = smux_list_windows(sa.id)[0]
val pa = smux_list_panes(sa.id, wa.id)[0]
# Deliberately unusual geometry: no inherited console coincides with it.
expect(smux_resize(sa.id, wa.id, pa.id, 97, 31).is_ok()).to_equal(true)
val shell = if _windows(): "cmd.exe" else: "/bin/sh"
val spawned = smux_pane_spawn_pty(sa.id, wa.id, pa.id, shell)
expect(spawned.is_ok()).to_equal(true)
expect(smux_pane_is_pty(sa.id, wa.id, pa.id).unwrap()).to_equal(true)
var pty_seen = ""
if _windows():
    expect(smux_send_text(sa.id, wa.id, pa.id, "mode con\r").is_ok()).to_equal(true)
    pty_seen = _squeeze(_await_capture(sa.id, wa.id, pa.id, "Columns"))
    # Produced by the console host from the ConPTY size; not in the input.
    expect(pty_seen).to_contain("Columns: 97")
else:
    expect(smux_send_text(sa.id, wa.id, pa.id, "tty\n").is_ok()).to_equal(true)
    pty_seen = _await_capture(sa.id, wa.id, pa.id, "/dev/")
    # A device path. A pipe can never produce one, and it is not in the input.
    expect(pty_seen.contains("/dev/")).to_equal(true)
    expect(pty_seen.contains("not a tty")).to_equal(false)
val _cp = smux_pane_close_pty(sa.id, wa.id, pa.id)

# --- B. pipe lane, same command ---
smux_reset_for_test()
val sb = smux_create_session("pipelane")
val wb = smux_list_windows(sb.id)[0]
val pb = smux_list_panes(sb.id, wb.id)[0]
expect(smux_resize(sb.id, wb.id, pb.id, 97, 31).is_ok()).to_equal(true)
expect(smux_pane_is_pty(sb.id, wb.id, pb.id).unwrap()).to_equal(false)
if _windows():
    expect(smux_pane_spawn(sb.id, wb.id, pb.id, "cmd.exe", ["/q", "/k"]).is_ok()).to_equal(true)
    expect(smux_send_text(sb.id, wb.id, pb.id, "mode con\r\n").is_ok()).to_equal(true)
    val pipe_seen = _squeeze(_await_capture(sb.id, wb.id, pb.id, "Columns"))
    # It answers -- but about the console it inherited, not the pane.
    expect(pipe_seen).to_contain("Columns:")
    expect(pipe_seen.contains("Columns: 97")).to_equal(false)
else:
    expect(smux_pane_spawn(sb.id, wb.id, pb.id, "/bin/sh", []).is_ok()).to_equal(true)
    expect(smux_send_text(sb.id, wb.id, pb.id, "tty\n").is_ok()).to_equal(true)
    val pipe_seen = _await_capture(sb.id, wb.id, pb.id, "not a tty")
    expect(pipe_seen.contains("not a tty")).to_equal(true)
    expect(pipe_seen.contains("/dev/")).to_equal(false)
val _c = smux_close_pane(sb.id, wb.id, pb.id)
```

</details>

#### the PTY child's terminal size is the pane geometry it was spawned with

- Verify: the child's own size query reports the rows/cols smux set
   - Expected: smux_resize(s.id, w.id, p.id, 97, 31).is_ok() is true
   - Expected: smux_pane_spawn_pty(s.id, w.id, p.id, "cmd.exe").is_ok() is true
   - Expected: smux_send_text(s.id, w.id, p.id, "mode con\r").is_ok() is true
   - Expected: smux_pane_spawn_pty(s.id, w.id, p.id, "/bin/sh").is_ok() is true
   - Expected: smux_send_text(s.id, w.id, p.id, "stty size\n").is_ok() is true
   - Expected: seen contains `31 97`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-SMUX_PTY_CONTROLLING_TERMINAL-001
step("Verify: the child's own size query reports the rows/cols smux set")
smux_reset_for_test()
val s = smux_create_session("geom")
val w = smux_list_windows(s.id)[0]
val p = smux_list_panes(s.id, w.id)[0]
# Deliberately unusual geometry: no default could coincide with it.
expect(smux_resize(s.id, w.id, p.id, 97, 31).is_ok()).to_equal(true)
if _windows():
    expect(smux_pane_spawn_pty(s.id, w.id, p.id, "cmd.exe").is_ok()).to_equal(true)
    expect(smux_send_text(s.id, w.id, p.id, "mode con\r").is_ok()).to_equal(true)
    val seen = _squeeze(_await_capture(s.id, w.id, p.id, "Columns"))
    # Both numbers come from the ConPTY size smux passed; neither is typed.
    expect(seen).to_contain("Lines: 31")
    expect(seen).to_contain("Columns: 97")
else:
    expect(smux_pane_spawn_pty(s.id, w.id, p.id, "/bin/sh").is_ok()).to_equal(true)
    expect(smux_send_text(s.id, w.id, p.id, "stty size\n").is_ok()).to_equal(true)
    val seen = _await_capture(s.id, w.id, p.id, "31 97")
    # "31 97" is produced by the kernel from the winsize smux passed to
    # openpty. It appears nowhere in the input line.
    expect(seen.contains("31 97")).to_equal(true)
val _cp = smux_pane_close_pty(s.id, w.id, p.id)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
