# Grouped input control V1 manual

Status: NOT_RUN. Source acceptance only; no runtime or full daemon PASS.

- `test/01_unit/lib/io/process_input_control_v1_spec.spl`: three real invalid-ref
  cases; mutation/query rejection and write-turn owner/attempt preservation.
- `src/runtime/test/process_input_control_v1_selfcheck.c`: actual same-registry
  transport fixture. Link normal CoreC owners; the fixture includes
  runtime_process.c exactly once, so omit that separate TU. No fake runtime array
  providers. Exact finite build/run recipe requires root allocation first.
- The fixture uses existing native bind/claim/publication with a real child PID
  and test-owned pipe read endpoint. It does not execute an admitted broker or
  claim cgroup/tree termination proof. Test-only slot teardown is not production
  cleanup. Copied legacy grouped writers are refused before inherited locks,
  including fork before enable. No privileged namespace/identity setup.
- Actual pipe saturation must produce Recorded0 and consume the attempt. Exact
  bytes confirm partial range delivery. Revoke must reject later writes and
  same-revision reinstall; higher revision resets current sequence while retaining
  the prior result. Duplicate and other preflight rejection must leave it intact.
- EPIPE must leave a known Recorded0 with error, not terminate through SIGPIPE.
  Expired writes must be Rejected without consuming a new attempt. Stale copied
  generation must not operate on a new slot. No automatic retry on Unknown.

Pending evidence must record exact source/producer/binary hashes, commands,
logs/exits and bounded timing under CPU0-4. No build/run is currently authorized.
See [design](../../../../05_design/process_input_control_v1.md) for remaining
facade, concurrency, signal-fault and application-integration qualification gaps.

Cycle2 SIGPIPE repair: EPIPE drains whenever SIGPIPE was not pending before the
write, regardless of any prior ignored disposition. A concurrently changed
ignored-to-default disposition cannot justify skipping the drain. One zero-time
sigtimedwait returning SIGPIPE or EAGAIN permits mask restoration; EINTR/other
uncertainty retains the blocked mask and Recorded known prefix with error. The
native fixture links `--wrap=write` to change SIG_IGN to SIG_DFL immediately
before the REAL write to an actually readerless pipe, and asserts Recorded0,
error and no pending SIGPIPE. This regression is authored NOT_RUN; it is not
a general signal-configuration or native runtime campaign.
