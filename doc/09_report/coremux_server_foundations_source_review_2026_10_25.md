# CoreMux server foundations source review — 2026-10-25

STATUS: WARN / NOT_RUN. Independent first-cycle review of the eleven-path foundation freeze, based on61e47484277f98437f1f5090c94fb343bf51b4bc. All eleven actual hashes matched. Historical v1 had two open P2 findings. The appended v2 focused review closes both; no remaining scoped P0/P1/P2 identified. Historical findings and exact pins remain below. Fifteen scenarios are authored, zero executed. No source edit, compiler/build/helper/native/product/test launch or commit occurred. The committed SDK lane was not edited.

Freeze: `build/review/coremux-server-foundation-source-v1.sdn`.

| Path | SHA256 |
|---|---|
| src/os/apps/smux/api.spl | cf50c43cb5b3afafc7f0e80692384c51b35b355003b3a676cc67748df08d232e |
| src/os/apps/smux/service_revision.spl | cbca271d7e84aa0887320bf8ae51c50d1c6aa273315a2e46793b37c3eafee18e |
| src/os/apps/smux/client_attachment_service.spl | 32af86a557a6e84ec7b9cac0f1b1d47022fe40d306e82098ffda954464a5ad05 |
| src/os/apps/smux/core_mux_owner.spl | 32eea862bb94a2e0630d52742305f794c4f81a383e30b1bea3435bd1a8dae41b |
| src/os/apps/smux/core_mux_leases.spl | 5e0b370ccf0fce1862bea921052a23474d6459569131f22d17361797314d7fb9 |
| src/os/apps/smux/core_mux_requests.spl | ce17f1632cd16a4d1a36774d5f60c1d3c7394cb5f27e4da98307cc663288c06a |
| src/os/apps/smux/interactive_protocol.spl | 6b673c917895bcdca2999adea99e3aef877c26589455c68d8e52defd03753b41 |
| src/os/apps/smux/interactive_client.spl | ce020c64c93a9ae8d4bb008a66cdc923b7c2b8fa048b1c6ced3bfca5a1ea3eab |
| test/03_system/tools/smux_coremux_owner_spec.spl | b18b96867d8146d3a1eba4a390236a33cb236714a9de0bcf9a445fb6bc5db7d6 |
| doc/06_spec/03_system/tools/smux_coremux_owner_spec.md | 3d2f23210fae3975f92ef5b89652f616471a657128e4ccf42fdfac253cc4b241 |
| doc/09_report/coremux_server_foundations_source_2026_10_25.md | a36ceef47bf33f1f62ce0e09cc3bedd3b1bfe6b144dc034d420d35370ed3b3b0 |

## Findings

### P2-01 — same-metadata attachment updates reorder clients and spuriously advance revision

`src/os/apps/smux/client_attachment_service.spl:51–52` and unmanaged attachment replacement near the end of that file; `service_revision.spl:100–105`; publication at `api.spl:295–301`.

With clients ordered[A,B], resize leased A to its existing dimensions. The transform renews A's heartbeat but also removes A and appends the same attachment, producing[B,A]. Publication compares ordered slots and increments configuration revision although client/session/attachment/dimensions have not changed. Same-metadata unmanaged reattachment has the same order churn. This violates the promised no-op/heartbeat exclusion and can spuriously reject a concurrent expected_revision request as stale.

Preserve attachment position using in-place value replacement, or return the original ServiceState for exact metadata no-ops while separately retaining the renewed lease value. Genuine new generation, session reassignment or dimension changes must still publish a revision. Add a two-client no-op control and distinguish it from an actual resize and leased re-admission. The existing heartbeat test uses empty ServiceState and cannot expose the slot reorder.

### P2-02 — revision exhaustion blocks checked split compensation

`src/os/apps/smux/api.spl:459–476,483,578,587`; writable predicate `service_revision.spl:30–33`.

At revision MAX-2, split is writable and can resize the existing child, publish a new empty pane and save its exact checkpoint. Publication advances to MAX-1, the reserved cleanup boundary. The following child spawn is correctly refused because new irreversible work is no longer writable. However, `smux_rollback_split` also rejects at its writable check before inspecting the saved checkpoint, so the caller cannot compensate the admitted split through its checked rollback path. The failed composite operation leaves its earlier resize/new empty pane instead of restoring prior geometry using the reserved cleanup authority.

Treat validated checkpoint compensation as cleanup, or reserve enough revision authority before starting the whole composite operation. Retain freshness, no-child/new-pane, ownership and geometry checks; do not reopen ordinary mutation/spawn authority or wrap the revision. Add a boundary control showing fresh work is refused while the exact pending split can still compensate. This is a source-derived counter-boundary sequence, not an executed repro.

## Publication and integration observations

The API retains the single authoritative ServiceState. Every observed assignment publishes through `_publish`; the new revision object holds comparison metadata rather than another service/controller copy. Immediate before/after comparison catches legacy ABA operations even when later state returns to its initial geometry. Session/window/pane/client identity, geometry, focus, presentation, native handles and child_incarnation participate. Output content/input queue progress and metrics are excluded. Attachment owner/generation identity participates while heartbeat deadlines are excluded; P2-01 is the remaining extraction interaction.

Cleanup/quarantine intent participates in publication. Revision saturation marks authority invalid without wrapping; epoch reset invalidates old owner references even if object names are reused. Normal creation, spawn, geometry, presentation and input admissions preflight writable authority; checked close/detach/reap paths remain available. P2-02 is the missing split-compensation exception. The child incarnation field is observed from the existing service owner rather than synthesized by the revision module.

Attachment helpers return explicit value updates for the API to publish. Secure entropy initialization remains behind the approved Sosix facade; failures return before attaching. Cleared-recipient notifications are carried separately. API callers retain the returned lease state. The scoped interactive changes filter independent-hidden plus zoom-occluded panes, reject input to each and recognize only exact owner visibility refusals for reselection. Successful view recovery resets input-prefix state and does not replay the refused input. Authentication/transport failures do not become recovery success.

Presentation and sized split are connected through their previously reviewed owner helpers, and API publication/quarantine occurs after those checked results. This review is not a new admission of changing capture/PTY internals or the complete mandatory CoreMux provider.

## Lease and receipt foundations

CoreMuxOwner stores namespace, authority and request metadata only, never ServiceState/native child owners. It requires explicit Smux/ExistingOnly scope and installed mandatory descriptors before publishing a connection lease. Entropy/time and the installed descriptor set remain responsibilities of the configured server composition; constructing a record is not endpoint authentication or qualification.

Lease state bounds live entries to4 and total live/retained entries to16. Tokens bind owner incarnation, monotonic serial and supplied validated nonce. Serial exhaustion refuses; expiry retention starts at the original deadline, not late observation. Revoke does not slide retention. Renewal rechecks completion-time liveness and cannot revive an expired/retired token. Wrong owner generation and monotonic regression refuse. Maintenance retires authority on API epoch/validity changes, returns resource-cleanup token identities and does not pretend to close children itself. The route must commit maintenance even when the following request is refused.

Arbitrary nonzero request IDs are accepted without increasing-order assumptions. Matching existing operation/payload replays the retained binding and original deadline; changed payload collides. Reserve occurs before effects. Normal entries cannot consume the final per-lease disconnect slot or the global control reserve. Defaults are4096 IDs per lease,8192 global entries,128MiB charged bytes and16 control slots, with lower accepted fixture limits. Live IDs are never evicted. Completion replaces reserved response charge with actual response bytes; retired normal completions discard full payload/response but keep typed status. Pending retired payload remains until completion/retention expiry. Disconnect retains exact payload/response for identical replay. Forget refuses executable nonretired bindings and recomputes charge for survivors.

The byte policy charges a conservative32768-byte receipt allowance plus request/result or reserved result buffers. Receipts limit detail to1024 bytes and affected entries to32 with bounded IDs. Control payload/reply ceilings fit the131072-byte reserved allowance. This is bounded source accounting, not a measured process RSS ceiling: actual array/runtime representations, copies and latency still require the admitted runtime/N2 evidence. Global pressure may require fixed retention expiry; the code does not claim unlimited rollover progress while every retained quota is occupied.

Expired/revoked tokens can reach only authenticated retained status or an already-bound identical Disconnect replay. Unknown IDs return Unknown without invented operation/affected state. Fresh effects under old tokens remain refused. Full dispatch must honor reservation.replay/pending and never execute a duplicate binding again; no listener or provider is implemented by this freeze.

## Specs, scheduling and final disposition

The fifteen authored scenarios use actual production revision/lease/ledger functions and selected existing API operations. They cover legacy zoom ABA, metadata versus output/input changes, hidden presentation input, exact non-replay recovery predicates, quarantine/counter arithmetic, lease expiry/clock/incarnation, incomplete mandatory admission, arbitrary IDs/collision, full typed receipt preservation, bounded-byte refusal, reserved disconnect/fresh-lease rollover, unknown IDs and reset retirement. The123 synthetic child identity is explicitly pure data and is not passed to a native owner. No fake native-effect success, replacement provider or unconditional placeholder pass was identified. The rollover fixture uses reduced real production limits; it does not execute4096/8192-entry load or native cleanup. Manuals accurately retain authored/NOT_RUN status.

The scheduling note correctly requires one persistent owner loop with maintenance/heartbeat work every iteration, bounded per-connection I/O and global work, original absolute frame/request deadlines, bounded queues and resumable native steps. A trickled frame must not synchronously monopolize the owner. Unbounded native operations remain a real integration blocker, not something this foundation or a future unreviewed worker can conceal. No fairness, latency, provider/listener, process-tree cleanup or N2 claim follows from this plan.

Final cycle1 disposition: two open P2 source findings; P0/P1 none identified in this bounded freeze. Correct and freeze the narrow delta for rereview. STATUS remains WARN / NOT_RUN with15 authored/0executed. Full provider/listener/capability, actual SDK integration and runtime qualification are explicitly outside this result.

## Cycle2 focused rereview — final scoped source disposition

Freeze: `build/review/coremux-server-foundation-source-v2.sdn`. All11 actual hashes matched. Six pins changed (three production files, spec, manual, author report); five production pins remain identical to v1. Review was limited to the two corrections and new/changed controls; the unchanged lease/ledger/interactive audit was not repeated.

| Path | v2 SHA256 |
|---|---|
| src/os/apps/smux/api.spl | c9d4d1ef5b8881f034daf18351d5fcae842974fc37543528b426193faedcf3b8 |
| src/os/apps/smux/service_revision.spl | f10fea7f10dfa627768c8866ee468f819401fbd25758d8e131452dc766ec82e1 |
| src/os/apps/smux/client_attachment_service.spl | 3eec16e36a4cbe2cad5f5c004636d1425d62f5374cee327695bc741f46035f3d |
| src/os/apps/smux/core_mux_owner.spl | 32eea862bb94a2e0630d52742305f794c4f81a383e30b1bea3435bd1a8dae41b |
| src/os/apps/smux/core_mux_leases.spl | 5e0b370ccf0fce1862bea921052a23474d6459569131f22d17361797314d7fb9 |
| src/os/apps/smux/core_mux_requests.spl | ce17f1632cd16a4d1a36774d5f60c1d3c7394cb5f27e4da98307cc663288c06a |
| src/os/apps/smux/interactive_protocol.spl | 6b673c917895bcdca2999adea99e3aef877c26589455c68d8e52defd03753b41 |
| src/os/apps/smux/interactive_client.spl | ce020c64c93a9ae8d4bb008a66cdc923b7c2b8fa048b1c6ced3bfca5a1ea3eab |
| test/03_system/tools/smux_coremux_owner_spec.spl | 976d9d5881a87fd74ed5bfcfa693f51040fb36da9cd6b938009aba7fde14a6ae |
| doc/06_spec/03_system/tools/smux_coremux_owner_spec.md | 98aa50f93ba512bada8d0457d5637e23b43c19dca414bd40591d9bf3fcd90790 |
| doc/09_report/coremux_server_foundations_source_2026_10_25.md | e642697a09e1908b94f941b62d36a316e79c2f9e40f8ca91c624536a153b0f65 |

P2-01 is source-closed. `client_attachment_service.spl:26–38` now rebuilds the bounded attachment slots in their original order, replacing only the target index. Existing leased attach, same-size leased renewal, real resize and unmanaged reattach use this same helper. Only the final ServiceState is published. Same metadata therefore compares equal while the separately returned lease state retains renewal. Changed dimensions and a new leased generation still advance configuration identity. Existing ServiceState client add/remove constructors preserve session/window/pane owners, counters and metrics during this local rebuild.

Two new real-API authored controls use clients A and B. They require unchanged revision and stable order for same-size resize/reattach, one tick for changed dimensions, a new token/generation on leased reattachment, refusal of the old token, and continued authority for the unaffected peer. These are actual API calls in authored source, not executions in this review.

P2-02 is source-closed. `api.spl:482–507` removes the fresh-work writable refusal from checked split rollback. It still refuses closing owners, locates the exact service-owned session/window/added-pane checkpoint, calls the production `service_revision_rollback_allowed` gate, then runs the existing ownership/geometry/presentation/focus/native-child freshness validation before compensation. The pure gate permits positive initialized clocks at reserved/saturated values only when checkpoint authority exists and the owner is not closing. It does not accept a caller-supplied replacement state, allocate a new identity, or authorize new split/spawn work. Successful compensation removes its checkpoint and publishes through the existing saturating revision owner; invalid authority stays invalid and does not wrap or reuse a revision. Failed native compensation still preserves ownership and enters quarantine.

The new rollback control obtains before/split/restored snapshots through the real API at its ordinary counter, verifies the added pane is gone and the checkpoint cannot be replayed, then composes those actual snapshots with the production gate/publication functions at MAX−2, MAX−1 and MAX. It checks missing-checkpoint/closing-owner refusal, reserved compensation, saturation and continued fresh-work refusal. This is deliberately not a private-global counter-injection or native exhausted-owner execution test. It would detect changing the tested pure gate back to the fresh-write predicate; an additional independent API preflight regression still requires connected-path source review or a future admitted exhausted-owner test.

Final scoped findings: no remaining P0/P1/P2 identified. Historical v1 findings/pins are preserved. The v2 fixture now has18 authored scenarios,0executed. Actual native resize/failure compensation, exhausted-owner execution, server fairness/listener/dispatch, provider capability admission, full cleanup and N2 remain NOT_RUN. No production edit, compiler/build/helper/native/product/test launch or commit occurred. STATUS remains WARN / NOT_RUN; source closure is not a full provider or pipeline PASS.
