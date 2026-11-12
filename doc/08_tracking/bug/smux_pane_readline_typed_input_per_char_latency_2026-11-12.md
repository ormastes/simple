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
(no readline) under ConPTY never completed the read within 40 s.
