# Enter to a cooked-mode `read -r x` in a smux ConPTY pane never completes the read

## Status

verification-pending 2026-11-13 (lane smux-enter). NOT reproducible on
release/1.0.0 `d3a686cd934`; a regression spec now guards it. Windows 11,
smux PTY backend, Git-for-Windows `sh.exe`, phase-1 seed.

## Origin

Side observation in
`smux_pane_readline_typed_input_per_char_latency_2026-11-12.md`: "a CR sent to
a cooked-mode `read -r x` (no readline) under ConPTY never completed the read
within 40 s". No reproducer was recorded with it.

## Measured (2026-11-13)

Spec `test/01_unit/os/apps/smux/pane_cooked_read_enter_spec.spl`; Enter is
sent as `\r` (`pane_command_state`, PTY panes).

| shape | paced (current) | pacing disabled (`paced = false`, temporary) |
|---|---|---|
| `sh -i`, then `read -r x; echo got=$x`, then `valQ7` + Enter | 0.04-0.06 s | 1.46 s |
| pane command `sh -c "read -r x; echo got=$x; sleep 3"`, then `valN9` + Enter | 0.07-0.10 s | 0.07 s |

Neither CR/LF translation nor the paced flush holding back the last chunk
stops the read from finishing: ConPTY turns `\r` into Enter, and the cooked
read returns. The one red run I saw came from a spec quoting error: `\$x`
reached `sh` as a literal `\$x`, so `got=$x` was printed without the value.
A probe with that quoting error looks exactly like "the read never
completes", which is the likely source of the original observation.

## Disposition

No product change. The regression spec stays (budget 5 s for both shapes).
Close as not-reproducible once a native (self-hosted) run of the spec is also
green.
