# Parser binary inspection has no single atomic input/process authority

**Status:** source gap; EODL REQ-016 and NFR-012 unqualified.

The selected inspector contract requires one identity-owned process to bind a
pinned executable, exact argv and environment, one immutable bounded stdin
input, complete stdout/stderr captures, terminal status, and reap before
issuing inspection authority.

Current source divides those facts across incompatible owners:

- `rt_process_owned_start_pinned_v3` in
  `src/runtime/runtime_process_owned.c` accepts a pinned executable and one
  copied input, and its V3 receipt reports accepted/written input bytes and
  stdin closure. Its process start uses inherited environment and has no exact
  pinned-cwd/environment request contract.
- `rt_process_observation_v4_start_pinned_value` authenticates executable and
  cwd pins plus a canonical exact-environment request, but `Pov4Request` and
  `ProcessObservationRequestV4` contain no stdin input or input digest/count.
  The V4 start path passes no input to its process engine. The fixed V4
  64-word receipt has no stdin-completion fact; word 63 is reserved and the
  Simple decoder rejects a nonzero value.
- `parser_external_inspection_tool_owner_start_v1` correctly returns
  `ProcessPortUnavailable`; its join rejects caller-supplied captures. Neither
  V3 nor V4 can be relabeled an authoritative inspection process receipt.

## Required repair

Implement a **versioned process inspection owner** that atomically copies and
hashes one bounded input at start, binds it to the exact pinned tool/argv/
environment/cwd request, pumps stdin concurrently with bounded stdout/stderr
draining, records exact write/close and terminal/reap facts, and retains an
opaque lease through collection. Keep V4's fixed packet semantics intact;
use a new request/receipt version or an explicitly reviewed versioned
extension. The compiler inspector may mint a token only from that retained
owner and two complete, independently captured readobj/objdump executions.

Acceptance includes short write, EPIPE, child exit before read, full pipe
backpressure, stdout/stderr overflow, timeout/cancel, failed reap, wrong tool
pin, changed environment, and stale/forged lease negatives. Passing V3 input
tests and V4 exact-environment tests separately does not close REQ-016.

Implementation order and protocol decisions are in
`doc/03_plan/compiler/parser_inspection_atomic_input_owner_2026-09-27.md`.
