# Electron open_file_dialog blocks on stdin with no timeout and silently drops unrelated IPC

## Status
Open.

## Severity
Medium — real hang trap, currently unreachable (zero production callers), but would hang the calling thread the moment something wires it up (e.g., a menu action).

## Summary
`src/app/ui.electron/main.spl:154-178` (`ElectronMain.open_file_dialog`) prints a file-dialog IPC request then blocks in an infinite `while true` loop on `rt_stdin_read_line()` waiting for a response line starting with `FILE_DIALOG_RESULT_PREFIX`. There is no timeout, no deadline, and **any other IPC line that arrives while waiting is parsed and silently discarded** (`_: pass_dn`). If the Electron bridge (`bridge.js`) never emits the expected response (promise never settles, window destroyed mid-dialog, malformed JSON, IPC truncation), the calling thread hangs forever. Additionally, **every intervening IPC event (mouse move, click, resize, other-window action) is read from stdin and dropped** — a lost-event pattern, not just a lost-wakeup.

## Evidence
- **main.spl:154-178**: `open_file_dialog()` loops `while true: val line = rt_stdin_read_line()` with no timeout or deadline.
- **main.spl:36-37**: Match statement discards unmatched events with `_: pass_dn` — any non-file_dialog_result line is consumed and dropped.
- **bridge.js:69-71**: The bridge correctly routes success and `.catch()` through `sendToSimple({type:'fileDialogResult',...})`, so the common path is fine.
- **grep -rn "open_file_dialog"**: Zero callers in `src/` or `test/` — the live Electron async loop (`async_app.spl`) never invokes this.

## Architectural Risk (H2)
A second independent stdin reader exists: `src/app/ui.ipc/async_handler.spl:19-43` (`start_ipc_reader`, runs on a background thread). Both call `extern fn rt_stdin_read_line()`. If `open_file_dialog` is ever wired up and runs concurrently, stdin lines can be race-stolen: the background reader thread could consume the `file_dialog_result:` line intended for the dialog, forwarding it to `event_channel` instead, so `open_file_dialog` would hang even though the bridge replied correctly.

## Failure Scenario
The moment something wires `open_file_dialog` into a live menu action or keyboard shortcut, pressing that action hangs the entire app until the dialog is somehow resolved (user or bridge timeout). All other IPC events arriving during the hang are lost.

## Next Step
Route open-file-dialog requests through the async_handler reader (`ui.ipc/async_handler.spl`) with a deadline instead of a private stdin loop. Consolidate stdin reading to a single, properly-scoped reader with deadline support. Ensure all abandoned operations send explicit timeout errors back to callers.
