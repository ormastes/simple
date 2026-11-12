# Typed input to a readline shell in a smux ConPTY pane echoes at ~0.25 s per character

## Status

Open 2026-11-12 (lane caret-capture). Windows 11, smux backend, Git-for-Windows
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
