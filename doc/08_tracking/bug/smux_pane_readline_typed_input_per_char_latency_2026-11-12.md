# Typed input to a readline shell in a smux ConPTY pane echoes at ~0.25 s per character

## Status

verification-pending 2026-11-12 (fix lane smux-readline; originally filed by lane caret-capture). Windows 11, smux backend, Git-for-Windows
`sh.exe` 5.3, phase-1 seed. Not a smux capture defect.

## Measured

Probe (`build/probe_wide.spl`, untracked): `agent_attach(..., "exec sh -i")`,
then `send_to_pane` of `echo Q<n W>_$((n+0))` and time until the capture shows
the output line.

| typed chars | readline (`sh -i`) | `sh --noediting -i` |
|---|---|---|
| ~56 | 8.9 s | 2.4 s |
| ~96 | 20.5 s | — |
| ~176 | 64.3 s | 3.5 s |

Owner instrumentation (temporary, reverted): the PTY write accepts the whole
command at once (`pty_write_some` returns the full byte count), every owner
`smux_poll_output` turn stays under ~330 ms (mostly < 50 ms), and the ConPTY
output for the command arrives as ONE chunk ~20 s after the write. So the
bytes are delivered immediately and nothing is dropped; the shell itself
spends ~0.25 s per character before echoing. Wrapping the command in bracketed
paste (`ESC[200~ ... ESC[201~`, the child had `?2004h` on) did not change the
latency (80 W: 23.5 s).

## Effect

A 300-column typed command takes ~75 s, over the 30 s `wait_for_pane_text`
window of `workspace_recovery_system_spec`; that example now produces the wide
line with a short command (`printf %0300d 0|tr 0 W;echo _$((1+1))`).

## Next step

Find what readline's raw-mode read under MSYS/ConPTY waits on per character
(candidate: readline's typeahead check `_rl_input_available`, a 100 ms
`select` timeout per inserted char, if MSYS console `select` does not return
early on pending input). If confirmed, the smux pane launch can set the
child's console/readline mode accordingly, or send long commands through a
path that does not go through per-key insert.

## Root cause (2026-11-12, lane smux-readline)

Cost depends on how many console input records are still QUEUED, not on any
terminal query or on TERM. In-process probes on `smux_pane_spawn_pty`:

- one key at a time: echo in ~30 ms; `TERM=dumb/xterm-256color/cygwin`,
  `INPUTRC=/dev/null`, `bash --norc`, `keyseq-timeout 0`, `input-meta off`,
  bracketed paste, and win32-input-mode (`?9001h`) encoded keys: no change;
- raw `dd bs=1`, `read -n1`, `read -t 1 -n1` loops over 120 queued bytes:
  < 1 s; one-char writes by the child: 0.1 s for 120;
- readline (`sh -i`, `read -e`) over the same queued bytes: 40 chars 3.6 s,
  120 chars 30 s, 200 chars 66 s (quadratic), with no echo at all until the
  queue is empty.

So each readline key read (its `pselect`) pays for every record still pending
in the MSYS console input layer under ConPTY, and handing the whole command to
ConPTY at once makes typing O(n^2). Echo-gated chunking proves it: 4-byte
chunks, each sent after the previous one echoed, type 200 chars in ~4 s.

## Fix

`src/os/apps/smux/pane_io_service.spl` `_flush_input`: Windows PTY panes get
paced input — at most 4 bytes per write (`pane_input_paced_len` in
`input_queue.spl`, never splitting an ESC sequence or a UTF-8 scalar), the next
chunk going once the child has produced output since the previous write. A
child silent for 500 ms is treated as non-echoing and gets unpaced writes
until it outputs again. Spec:
`test/01_unit/os/apps/smux/pane_readline_typed_input_latency_spec.spl`
(200 typed chars into `sh -i` < 5 s): before 66.5 s, after ~4.0-4.3 s.

Side observation, not fixed here: a CR sent to a cooked-mode `read -r x`
(no readline) under ConPTY never completed the read within 40 s. Filed as
`smux_pane_cooked_read_enter_never_completes_2026-11-13.md` (not reproducible on 2026-11-13).

## Re-measurement 2026-11-13: 6.1-6.8 s, cause is the child, not smux

The spec now reports 6.08-6.8 s against its 5 s budget. Nothing on the smux
pacing path changed since #8677: `git log src/os/apps/smux` shows only
`4888189d145` (POSIX hangup batching in `child_lifecycle.spl`), and the spec's
only later edit is `51835b9d84f` (lighter capture poll), which was part of #8677.

Measured on release/1.0.0 `e1df3719a2d`, phase-1 seed, host CPU load 15 %:

| condition | typed200 seconds |
|---|---|
| spec alone | 6.47 |
| spec while the whole smux directory runs | 6.62 |
| probe, chunk 1 byte | 7.08 |
| probe, chunk 4 bytes (shipped) | 6.79-6.84 |
| probe, chunk 8 bytes | 8.58 |
| probe, chunk 16 bytes | > 90 (never echoed) |

A per-write trace (temporary `print` in `_flush_input`) shows every 4-byte
chunk taking 105-130 ms from write to the 4-byte echo, i.e. ~26 ms per key
inside the MSYS readline child. Our own share is the poll period: with a 30 ms
poll the per-chunk times quantise to 111/148 ms, so smux adds one poll (~10 ms
with the spec's 5 ms sleep), not the bulk. The probe loop spent 3.4 s of its
6.8 s in `smux_capture_history`, running in parallel with the child.

Why pacing cannot reach 3 s here: per-key cost is ~25 ms at a queue depth of
1, and grows with depth (8 bytes -> ~43 ms/key, 16 -> runaway O(n^2)), so a
bigger chunk or two chunks in flight makes it worse, and a smaller one only
adds round trips. 200 keys x ~25 ms is ~5 s before smux does anything. The
4.0-4.3 s recorded in #8677 implies ~20 ms per key on that day's host state.

Status: open. The 5 s limit was NOT raised. A real fix needs the child to see
fewer key events (e.g. bracketed paste when the child has enabled DECSET 2004,
which changes `send_command` semantics and needs an owner decision), or a
cheaper MSYS console read path.
