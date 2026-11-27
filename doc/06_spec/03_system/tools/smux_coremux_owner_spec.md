# CoreMux server authority foundations

Source: `test/03_system/tools/smux_coremux_owner_spec.spl`.
Requirements: REQ-CMUX-002/004/005/008/010.
**WARN / NOT_RUN: 18 authored scenarios, zero executed.** This manually prepared
mirror follows the actual scenario bodies. Native SSpec, docgen and visual
capture are pending. No coverage percentage or persistent-provider PASS exists.

These controls exercise the real existing smux API and the new pure authority
state machines. They do not instantiate a replacement provider, manufacture a
child process, bind a TCP endpoint or qualify the full mandatory CoreMux port.

| Scenario | Meaningful observation |
|---|---|
| Attachment identity | A new attachment generation advances configuration; heartbeat deadline changes do not. |
| Two leased clients | Real API same-size renewal preserves order and revision; actual resize advances once; reattachment advances generation, rejects the old token and leaves the peer valid. |
| Two unmanaged clients | Real API identical reattachment preserves order/revision; changed dimensions advance once in the original slot. |
| Legacy ABA | Real API zoom→restore advances twice even when final geometry equals initial; empty output poll adds no configuration revision. |
| Content versus configuration | Actual record feed/input transforms do not change configuration; a new child incarnation does. Synthetic PID remains pure data. |
| Presentation and hidden input | Real API title/hide/show changes publish revisions; interactive list excludes hidden pane and input refuses it. |
| Recovery predicate | Only four exact owner visibility refusal forms permit reselection; auth, transport, wrong-pane and extra-text errors do not. |
| Quarantine and overflow | Cleanup intent advances revision; identical intent does not; exhausted writable authority cannot wrap or admit a new mutation. |
| Reserved split compensation | Real API split/checked rollback restores the surviving pane and consumes its checkpoint once. Those actual snapshots exercise the production clock at MAX−2/MAX−1, proving the reserved cleanup tick and saturation without injecting global revision authority. |
| Expiry and retention | Expired token cannot renew; retention starts at original deadline and reads do not extend it. |
| Clock and incarnation | Regressed monotonic clock and wrong owner generation refuse; reconnect issues a distinct token even with repeated test nonce input. |
| Mandatory admission | Empty installed capability set refuses before publishing a lease. No fake success descriptors are used. |
| Request identity | Arbitrary decreasing IDs are valid; identical pending replay retains the original deadline; changed bytes collide. |
| Retired receipt | Every original receipt field survives retirement, including partial cleanup, while normal payload/result bytes are released. |
| Byte reserve | Normal payload exceeds available byte budget before effects; reserved disconnect bytes remain usable. |
| Explicit rollover | Small configured per-lease quota fills; normal request returns Busy/NotApplied; reserved disconnect succeeds; a fresh lease progresses while old status survives fixed retention. |
| Unknown binding | Missing request ID yields Unknown without invented operation or affected resources. |
| API reset | Old connection authority retires when API epoch changes; renewal refuses while narrow retained status lookup remains possible. |

The rollover scenario uses the production functions with a three-ID lease
budget to exercise the same boundary without thousands of duplicate controls.
Production defaults allow 4096 IDs **per lease, including one disconnect ID**,
8192 global entries, 128 MiB accounted retained/reserved storage, and sixteen
global disconnect slots. Those sixteen slots are included in the global entry
limit. Each has 128 KiB reserved against normal-command admission. Storage
accounting includes a conservative fixed allowance per typed receipt plus
canonical request/result buffers and pending reply reservations.

At global capacity, new normal effects return Busy; fixed retention expiry
releases retired storage. Rollover is explicit disconnect/reconnect and does not
terminate background sessions. Normal execute replay is prohibited after
revocation; RequestStatus retains the exact compact receipt. Pending operation
payload remains until completion or final retention expiry. Only identical
disconnect replay retains its exact full response. Lost binding/authority is
Unknown, never evidence that an earlier effect was NotApplied.

## Native and composed gates still required

Run with a verified Phase 3 full CLI and explicit `--native-backend llvm` plus
`--library-mode nogc-sync-mut`, using canonical broad roots and normal resource
limits. Final commands and producer/runtime hashes belong to the root
coordinator. No seed or interpreter fallback is accepted.

The persistent listener/adapter is not bound in this foundation stage. Real
create→configured argv/cwd/env launch→literal send→capture→disconnect→reconnect→
checked kill, actual failed/deferred native cleanup, lost replies, clock behavior,
multiclient fairness and N2's 24-hour runs still require the real composed owner.
No authored state control replaces child observation, process-tree quiescence,
CareT/IDE integration, the tmux backend, or full mandatory-operation admission.
