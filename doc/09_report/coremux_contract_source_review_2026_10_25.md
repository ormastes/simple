# CoreMux contract source review — 2026-10-25

Status: **WARN / NOT_RUN — focused source review complete; no open scoped P0/P1/P2 findings**. Independent review of four additive contract files frozen at HEAD `7bc0826bf89d6f6b5a240468b1453435505f94a8`. No compiler, native test, helper, watchdog, or product process was launched. No production source was edited by the reviewer. Concurrent Smux/Caret zoom changes are outside this review.

## Scope and evidence

Reviewed against accepted option A/N2 in `doc/02_requirements/feature/caret_mux_tui.md`, `doc/02_requirements/nfr/caret_mux_tui.md`, the corresponding architecture/detail design, and the capability-interfaces skill and authoring guide. The context file executor was unavailable because its Node executable was missing; bounded local source reads were used instead.

All four source hashes independently matched `build/review/coremux-contract-source-freeze-v1.md`. The subsequent three spec/manual/design hashes matched `build/review/coremux-contract-complete-freeze-v1.md`. Existing D1 `core_v1.spl` and `validation_v1.spl` have no diff against HEAD. This preserves their declarations and callers; it is not an executed compatibility result. The design delta adds sixty lines without deleting prior content.

| Frozen source | SHA-256 |
|---|---|
| `src/lib/common/contracts/mux/execution_v1.spl` | `e6a33b634798b2d97b4ef2b44ce876d1231306708d6f31fc74be9b7b13628553` |
| `src/lib/common/contracts/mux/observation_v1.spl` | `1d6f833d627f31aeb1a24db8ceae921c8186b978b79ebcde8ab7a7befd1e0814` |
| `src/lib/common/contracts/mux/port_v1.spl` | `819f6b895e562654158f8556c2e347fec53d881edc8e42c36fecd320b58cf07e` |
| `src/lib/common/contracts/mux/request_validation_v1.spl` | `e66ae0ee8ff51c9e5d9cb87ee2b0af4032839fa5f38f004069c47d83573cd981` |
| `test/01_unit/lib/common/contracts/mux/core_execution_v1_spec.spl` | `f085416088b539606f8b8933ed9a29c38f4d55794710e35d312e5e197be48b0d` |
| `doc/06_spec/01_unit/lib/common/contracts/mux/core_execution_v1_spec.md` | `00dbc4a9c3398b8abfaa20f2d06c3b8e4d0dfba683fbf91f43f950a5c085870c` |
| `doc/05_design/caret_mux_tui.md` | `115b53bf71f718d1322fd82a8eeed8b60956394f885107b95d48eac1e5b4241b` |

## Initial v1 findings (all closed by v2 source correction)

1. **P2: disconnect validation loses request correlation.** `mux_validate_disconnect_v1` directly propagates errors from handle/deadline validators. Those errors carry `request_id: 0`, even when the disconnect request supplied a nonzero ID. The equivalent execute validator explicitly correlates every failure. Preserve the disconnect ID on every validation failure, including malformed handle and deadline, and assert the actual error fields in focused controls.
2. **P2: revoked-lease reconciliation contradicts the port admission rule.** `port_v1` requires a live lease on every call, while `MuxDisconnectV1` says successful disconnect revokes it, repeated disconnect returns retained outcome, and unknown completion must be reconciled through request status. The latter two actions cannot satisfy the former rule. Specify narrowly bounded receipt-only authentication for the exact revoked lease/incarnation/request, or another explicit recovery mechanism. It must not authorize new work, renew a revoked lease, expose another client's receipts, or revive an old owner generation. Retention expiry and owner loss must remain honest unknown/stale outcomes.
3. **P2: N2 lease expiry and renewal have no interoperable contract.** The full connection contains an opaque handle but exposes no finite lease duration/renewal cadence, and none of the port methods defines renewal behavior. A consumer cannot know whether ordinary query/poll traffic keeps its attached view alive or whether an idle controller needs an explicit action; a provider can retain crashed-client constraints indefinitely without violating the new method signatures/comments. Define a bounded owner-monotonic lease policy, how active consumers renew (an existing query/poll operation may suffice), and expiry cleanup of client capacity/view constraints while preserving background children. Expired tokens must never revive; a rebind/reconnect must issue distinct authority. This can be additive to the full contract without changing D1.

The design's appended full-contract section supersedes its older discovery-era `fn query`/standalone capabilities description. The frozen six-method `me query` port remains authoritative for transport state and capture ingestion.

4. **P2: the authored Unicode preservation case uses ASCII question marks.** `contract_launch` supplies `"???"` for `MUX_TEST`, and its preservation assertion expects the same text; the title fixture likewise uses question marks. The environment literal was independently read as codepoints 63,63,63, not a console-rendering substitution. The case/manual therefore does not exercise its claimed non-ASCII environment preservation. Use actual UTF-8 literals or the canonical byte decoder and assert the preserved non-ASCII values/bytes. This is a test-authoring gap, not evidence of a production Unicode failure.

## Focused spec/manual review

Eleven authored cases, zero executed. They call the actual pure production validators and command mapping: all thirty command variants and thirty-nine operation identities, target-owner/incarnation/kind refusal with error fields, deadline/ID/cell boundaries, launch data, distinct literal/paste/key intent, scalar/surrogate/function-key limits, capture extents/continuation, Partial/Unknown/Pending receipts, capability completeness and evidence preservation, Unsupported descriptors, and query/disconnect/event bounds. The Unicode case has the gap above; the disconnect case checks success correlation but does not cover the malformed nested-error path in finding 1. The author has been asked to add that negative coverage.

No provider stub, no unconditional pass, and no refusal gate represented as backend feature execution was found. Native descriptors are explicitly untrusted fixture data paired with NotRun, and that evidence status is asserted. These are legitimate representation controls; they do not prove authentication, unsupported-before-effects behavior, actual operation execution, deduplication, timers, or process cleanup. The manual preserves this boundary and marks docgen unexecuted.

## Other reviewed properties

The closed command sum covers all thirty mandatory command categories in the selected design. The operation inventory adds the nine connect/query/event/disconnect categories for thirty-nine mandatory descriptors. Required title, border, hide/show, rebalance, zoom, capture, notifications and lifecycle operations remain mandatory. The command-to-operation mapping has an explicit arm for every command. Optional terminal extensions are separate; no missing mandatory operation becomes optional.

The port has no default implementations or success bodies. `backend` is observational; all transport methods use `me`. A single composition-owned instance and immutable owner/incarnation/lease references avoid pairing copied mutable controllers. Public records and shape checks explicitly grant no authority. Ownership, membership, permission, current revision and actual support remain provider checks before effects. Representation-level capability admission accepts Native/Emulated separately from NotRun/Blocked/Qualified evidence; it does not certify a caller-supplied receipt or qualify a provider.

Relative request budgets are bounded and owner-clamped, with original deadlines retained for duplicate IDs. Payload mismatch on a repeated ID is invalid; expired/unknown receipts cannot prove NotApplied, and pending receipts cannot report final commitment. Partial/Unknown native effects remain distinct from validation-time NotApplied. The revoked-lease boundary identified in v1 is corrected as recorded below.

Launch has distinct executable/argv and explicit shell variants, bounded arguments/environment changes, and no join-and-resplit transport. Literal bytes, named/scalar keys, paste and submitted shell commands remain separate. Size/rectangle checks bound cell coordinates; target checks compare owner/incarnation/kind without pretending to prove live membership. The owner must still validate window/pane/client relationships and provider-specific limits. Shape checks reject malformed UTF-8 and controls in presentation text while preserving arbitrary literal input bytes.

Metadata snapshots do not drain output. Capture exposes content revision and ingestion separately from configuration revision; bounded continuation is pane/generation/options/revision-bound. Events have item/byte limits and an explicit reconciliation flag. No real capture, Unicode cell, rendering/ACK, child resize, cleanup, or backpressure behavior has been demonstrated by these types.

## Qualification limits

All native behavior remains **NOT_RUN**. These files contain contracts and pure representation helpers, not a usable Smux/Tmux provider, client/server binding, caller migration, or N2 qualification. D1's thirty-three authored controls and the new eleven cases remain unexecuted under this review. The bounded v2 correction received the focused source rereview recorded below. Mandatory backend/caller workflows, failure-before/after observations, lease crash recovery, restart/rebind rejection, Unicode/capture behavior, bounded queues, latency and the full 24-hour soak remain outstanding acceptance evidence.

## Focused v2 correction review

Cycle 2 reviewed only the corrections and changed test/documentation content. All seven files independently match `build/review/coremux-contract-complete-freeze-v2.md`; `execution_v1.spl` retains its v1 bytes and both D1 files remain unchanged against HEAD. The thirty commands, thirty-nine operation discriminants, and six provider signatures are unchanged. **All four v1 P2 findings are closed at the source-contract level.** No provider authentication, clock, cleanup, or execution result is implied.

1. Disconnect validation now has a checked inner helper and an outer error-correlation step. Both nested handle and deadline errors preserve the supplied request ID. Added negative assertions inspect ID, kind, NotApplied, absent observed revision, and empty affected objects.
2. The port and disconnect contract now explicitly limit revoked/expired-token access to retained status for an already-bound original request ID or identical retained disconnect replay. Authentication uses original token, owner incarnation and retained history. This exception permits no new effects, metadata, capture, events, renewal, or cross-client receipt access. Lost binding/outcome remains Unknown; reads do not extend retention, and all access ends when retention expires. The added pure receipt matcher checks original token/owner/generation/ID, while explicitly declining to authenticate those values.
3. `MuxConnectionV1.lease_terms` adds bounded lifetime, renewal cadence, receipt-retention duration and retained-receipt capacity. Renewal cadence is at most half the lifetime. Normal successful authenticated query/poll calls renew using owner-monotonic time; the transport retains the policy and polls while idle. Renewal rechecks liveness at completion so a late completion cannot revive an expired token. Failed calls and recovery reads cannot renew. Reconnect requires distinct authority. The duration/capacity validator and boundary assertions cover representation only. Actual expiry must still release client capacity/view constraints while preserving background children under NFR-CMUX-006; provider implementation and real crash tests remain required.
4. The environment fixture now contains actual Korean and emoji text. The preserved return value is checked against independent UTF-8 bytes `[237,149,156,240,159,152,128]`. This closes the ASCII-question-mark authoring gap without claiming a native Unicode execution result.

Fourteen focused cases are now authored, **zero executed**. Three added cases cover nested disconnect correlation, reconciliation receipt identity/Unknown semantics, and lease-term bounds. The manual describes these as pure representation checks and explicitly leaves idle renewal, expiry, retention, revoked-token refusal and no-revival tests to real provider qualification. There is no fake clock, fake provider, default success, or closed-gate backend pass in these tests.

### Final v2 pins

| Frozen path | SHA-256 |
|---|---|
| `src/lib/common/contracts/mux/execution_v1.spl` | `e6a33b634798b2d97b4ef2b44ce876d1231306708d6f31fc74be9b7b13628553` |
| `src/lib/common/contracts/mux/observation_v1.spl` | `0ca532566513b5f48415e76f9edf2a4956410d5d147d79f81072028b1ff7fd05` |
| `src/lib/common/contracts/mux/port_v1.spl` | `98bad4eda282cde80fb7dc1233908506696299a5dcb90b4b277f944a0ed1a60d` |
| `src/lib/common/contracts/mux/request_validation_v1.spl` | `fc5bf4472921a95a91715dce597a5cd21f58a34da6e2ddfe44f4005753b34df9` |
| `test/01_unit/lib/common/contracts/mux/core_execution_v1_spec.spl` | `2dd87f204af24118582ea71fecf41c5e8b8bada0e0c6a5dd7172c841d85aecfe` |
| `doc/06_spec/01_unit/lib/common/contracts/mux/core_execution_v1_spec.md` | `fa008023810967a01d010143a2c8122e94faf3c0c736b625ef6c18f7a3985b3e` |
| `doc/05_design/caret_mux_tui.md` | `7df92189752cde8ea80262ac75d87727049f33480801384610364a3f8321e12d` |
