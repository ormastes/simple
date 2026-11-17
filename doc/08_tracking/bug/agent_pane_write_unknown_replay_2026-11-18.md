# Agent pane Write: no replay protection after an Unknown native outcome (2026-11-18)

Found by the independent Opus review of #10082 (pre-existing since #10079).

`host-agent-pane-write` issues a fresh Input control lease per Write and reinstalls the native input gate. The Linux native
layer only ever records dispositions 0/1 (`src/runtime/runtime_process.c:4913-4970`); Unknown arises on the Simple side
(receipt unavailable/malformed). The pane write path never records into `owner.controls.input_attempts`, so
`primary-input-prior-outcome-unknown` (`smux_runtime_control_owner_v1.spl:147`) cannot fire for the agent pane, and a client
retry after an Unknown outcome gets a new revision and writes the bytes twice.

Fix direction: record the pane write attempt/outcome in `input_attempts` keyed by the signed binding uid and refuse the next
issue while it is Unknown (mirror the V5 connection input path), with an adverse spec. Status: FIXED (source authored, specs NOT_RUN) 2026-11-18. Resolution: not `input_attempts` (the owner issues a fresh lease per
Write, so its revision cannot identify a retry) but a client `writeId` bound into the request and a bounded per-lease ledger
owned by the agent (`HostAgentAttachmentV4.pane_writes`, `host_agent_pane_io_core_v4`): exact retry answered from the
record without a second native write, reused id with other bytes refused, evicted id refused as stale, unreadable ledger
refused. Specs: `host_linux_service_agent_v4_pr3b_lifecycle_spec.spl` (ledger describe), `runtime_agent_pane_v1_spec.spl`.
