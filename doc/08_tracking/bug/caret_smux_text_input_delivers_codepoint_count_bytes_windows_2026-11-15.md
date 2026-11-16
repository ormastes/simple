# smux text input on Windows delivers only as many bytes as code points; the tail stays queued

Date: 2026-11-15. Status: fix landed, verification-pending (native).

## Repro
`test/03_system/app/llm_caret/caret_terminal_bytes_live_spec.spl` drives
ESC [ A, Ctrl+B, Hangul, emoji and leader+`z` through `split_complete_keys` ->
`cs_terminal_keys_via` -> real `pane_send_raw` onto a real Windows smux
(ConPTY) pane running `test/fixtures/caret_workbench/hex_echo_stub.shs`
(child-computed hex, not PTY echo). Run: `bin/simple test <spec>`.

## Observed
The child read exactly `1b 5b 41 02 ed 95 9c f0` (8 of 13 bytes) and nothing
more; the child's own side log confirmed it (not a capture artifact).
`smux_input_status` then reported `queued:5` and never drained.

Three probe shapes, bytes sent vs delivered:

| sent bytes | code points | delivered |
|---|---|---|
| 13 | 8 | 8 |
| 7 (A, emoji, B, C) | 4 | 4 |
| 17 (no emoji; includes Hangul) | 15 | 15 |

Delivered byte count equals the number of code points and the tail of
(bytes - code points) stays queued, so this is NOT specific to emoji or to a
UTF-8 split. Order is preserved. Hypothesis (unconfirmed): a code-point/unit
count is used where a byte count is expected. Where to look:
`src/os/apps/smux/pane_io_service.spl:204-215` (`accepted` from
`pty_write_some`, then `pane_input_advance`, `input_queue.spl:84`) and the
native `write_some` behind `std.sys.pty`.

## Unblock condition
Terminal-surface bytes must arrive exactly; the spec must go GREEN unchanged.
smux is not a caret file, so no production edit was made in this lane.

## Not claimed
Windows seed-interpreter lane only; Linux/macOS/board not run.

## Fix (2026-11-15)

Root cause was not in the smux queue: `process_write_stdin_some`
(`src/lib/nogc_sync_mut/io/process_ops.spl`) passed `data.len()` (code points)
as the byte limit to `rt_process_write_stdin_some`. 13 bytes / 8 code points ->
bytes 0..8 written, then offset == limit forever (`queued:5`). New
`process_stdin_data_len` returns the byte length (`str_len`).

- Repro + generalization: `test/01_unit/lib/nogc_sync_mut/io/process_stdin_data_len_spec.spl`
  (RED 1/4 -> GREEN 4/4); `test/01_unit/os/apps/smux/input_queue_spec.spl` 12/12.
- Live: `caret_terminal_bytes_live_spec.spl` RED 0/1 -> GREEN 1/1 on Windows seed interpreter with the fix.
