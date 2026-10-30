# Smux window lifecycle source review

Independent bounded review against HEAD `d958cce328b`, 2026-10-25.
**Compilation and execution: NOT_RUN.** Nine authored scenarios, zero executed.
No native compiler, product, provider or test process was launched. Source
inspection does not qualify two-console recovery or native cleanup completion.

## Findings

**P2 closed in source: native fixture cleanup could be skipped.** The original
native rows asserted spawn/attach/send outcomes after child acquisition, and
the PTY row did not retry a failed original target during final cleanup. Both
rows now collect operation results and invoke bounded session-wide checked
cleanup before any post-acquisition assertion. That cleanup uses authoritative
in-process session presence, retries retained child authority through
`smux_kill_session`, and preserves cleanup errors as failures. It does not reset
metadata as proof of teardown. Original operation assertions remain distinct,
so eventual cleanup does not disguise an earlier failed lifecycle operation.

No remaining concrete P0/P1/P2 was identified in the bounded corrected delta.
Source-review status is **WARN**, because native and console qualification
remain unexecuted, not production verification PASS.

## Reviewed production behavior

- The child-close helper receives and returns a ServiceState snapshot without
  reading or committing the global registry. It clears native authority only
  after checked close success; false close preserves the original PID/fd for
  retry. Successful sibling teardown is retained during partial failure.
- Nonfinal window removal records closing state before teardown. Target input,
  queued writes, native drains, spawning, splitting, geometry mutation, focus,
  pane removal and split rollback refuse closing owners. Other windows retain
  their records. Pure removal refuses any target native authority before
  rebuilding the bounded registry.
- Final-window deletion delegates directly to session kill before taking a
  snapshot. There is no later stale window snapshot commit. Session teardown
  remains responsible for its clients, leases, notices and checkpoint pruning.
  Nonfinal success preserves those session-owned resources and removes only the
  target window's checkpoint and closing marker.
- Rebuilding preserves next-ID and metrics, complete survivor pane/window
  records and client attachments. Inactive-window removal preserves focus;
  active-window removal deterministically selects the first registry survivor.
  Session removal also prunes its pending-window markers.
- Remote kill validates session/window ownership and the existing managed
  envelope validates canonical session and lease before dispatch. Missing
  session remains an error reply to remote callers; the attached terminal only
  treats the exact authenticated response for its own stable session ID as
  normal session termination. Other lease and transport errors remain errors.
- Missing-window recovery queries survivors using the same lease and validates
  a current frame before committing new local selection. It resets copy state
  and the input decoder and does not replay the failed input or subsequent
  actions from that batch. Console restoration still uses its existing checked
  close/retry owner. Copy mode's historical snapshot is explicitly documented.

## Evidence limits

Pure refusal cases use synthetic authority only at the actual pure pruning
gate, never as native-close evidence. Protocol cases use actual public API and
dispatcher state, including lease refusal and replacement-frame validation.
They do not exercise the interactive console recovery loop. The two native
rows demand child-computed values, but remain unexecuted.

The design and plan explicitly retain actual independent two-console recovery,
deferred/failing close, mutation refusal during pending cleanup and a formerly
nonfinal-to-final retry as outstanding acceptance work. A finite retry loop does
not preempt a blocking native close; the external process-tree watchdog and
terminal/quiescence receipts remain mandatory. No authored or source-review
result may be reported as native PASS.

## Frozen reviewed input SHA256

| File | SHA256 |
|---|---|
| src/os/apps/smux/api.spl | b8f169076e40beb1a08e2974614c1a3156d8971049d772d1d908702a88b89062 |
| src/os/apps/smux/session_lifecycle.spl | 342c87badc83cbb84055c2aa539b71304530da826853b80376d566d7cd1ce9f6 |
| src/os/apps/smux/smux_remote.spl | 9dcb825ea08ab1d11d9545de96793a47c6659e9e59007c830232d42855711a44 |
| src/os/apps/smux/interactive_protocol.spl | e497404247925a6c0d128289d2a9ae2845a9f9238355b877215c15f4175a45fd |
| src/os/apps/smux/interactive_client.spl | d5c0a523f7cc6e3b9399ced0fab935944416b5ee3c4b93411c6977c4e229aa3a |
| src/os/apps/smux/child_lifecycle.spl | fa1f8b4af0acc2252838ebe3f961580660cb4d01b29647c8417e84900d96a48c |
| src/os/apps/smux/lifecycle_reply.spl | 8c1512e9536466ac7b6e7dd31140dec51dbd51d43850fa8bb98e9ee6c8f6fe97 |
| test/03_system/tools/smux_window_lifecycle_spec.spl | 1c5bc7a24583c7a4984c0472e2853d15b375a76da7ee097d880f9800af921ad7 |
| doc/06_spec/03_system/tools/smux_window_lifecycle_spec.md | f51b2a866ccceca27a63f312c86b63199b7b905100d037df399cbb5ffb86b587 |
| doc/05_design/smux_window_lifecycle_2026-10-25.md | ed4e53ea1b00f50281818570fdb7b003ce8db6c04a09f1eeb3c29a4f96cf299b |
| doc/03_plan/sys_test/smux_window_lifecycle.md | 3da4e33568462925ecce7a968b1bcc41e6db4e46ceb4ed262db5bf8bd0e8b506 |
