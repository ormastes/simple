# Agent pane Write: no replay protection after an Unknown native outcome (2026-11-18)

Found by the independent Opus review of #10082 (pre-existing since #10079).

`host-agent-pane-write` issues a fresh Input control lease per Write and reinstalls the native input gate. The Linux native
layer only ever records dispositions 0/1 (`src/runtime/runtime_process.c:4913-4970`); Unknown arises on the Simple side
(receipt unavailable/malformed). The pane write path never records into `owner.controls.input_attempts`, so
`primary-input-prior-outcome-unknown` (`smux_runtime_control_owner_v1.spl:147`) cannot fire for the agent pane, and a client
retry after an Unknown outcome gets a new revision and writes the bytes twice.

Fix direction: record the pane write attempt/outcome in `input_attempts` keyed by the signed binding uid and refuse the next
issue while it is Unknown (mirror the V5 connection input path), with an adverse spec. Status: open, specs NOT_RUN.
