# Sosix CoreMux client source review — 2026-10-25

STATUS: WARN / NOT_RUN. Current cycle3 disposition: both historical production P1 findings and both endpoint-spec P2 findings are source-closed; no remaining scoped P0/P1/P2 identified. The historical v1 review and exact pins below are retained; the appended v2 section supersedes its disposition. No compiler, native helper, product, test runner or SSpec was launched; runtime executions: 0. The existing server has no new framed route, so this report establishes neither provider compatibility in execution nor CoreMux qualification.

## Exact reviewed inputs

Freeze: `build/review/coremux-sosix-client-source-freeze-v1.md`. All four source SHA256 pins were independently read and matched:

| Path | SHA256 |
|---|---|
| src/lib/nogc_sync_mut/sosix/mux.spl | e470ea103fcd43e06d902c9453d05df2907ee1c1edefe516438131e683b87d2a |
| src/lib/nogc_sync_mut/sosix/mux/client_v1.spl | 2c93f8bbb9ee516010e8842a1a3a2c4f49fb7bf75a44f9b7a9cdd076ff113b12 |
| src/lib/nogc_sync_mut/sosix/mux/config_v1.spl | acf9d60c5cfebd1670ea1a38b88d7794b5182a615f01d8067954c9095b874ee3 |
| src/lib/nogc_sync_mut/sosix/mux/transport_v1.spl | d300b4945c1027c20e50e1f31b91f30a91a688cc80d3376352f9f12006ddfde8 |

Necessary boundary reads: CoreMuxV1 port; common request/discovery validators; wire envelope and request/result correlation contracts; existing NoGC TcpStream and Sosix monotonic-time owner. The separate eleven-file codec review is not duplicated or claimed here.

## Open findings

### P1-01 — issued connection handle is discarded before failed admission can retain cleanup authority

`client_v1.spl:94–98,114–115,147–151`.

A successful response can be correctly correlated and decode to a structurally valid Connection containing a valid owner-issued lease, but fail the subsequent request/result relation. For example, request max_reply_bytes=4096 and receive a small, well-formed Connection advertising max_reply_bytes=8192. The body can fit the actual4096 frame while its advertised limit exceeds the requested value. `wire_exchange_v1.spl:31` rejects that relation. The client returns Unknown at114–115; connect's `?` at147 returns before storing the connection at151. `recovery_handle()` therefore returns nil, and another connect on the same instance is permitted even though the earlier allocation is uncertain. A decoded valid Connection that fails the total deadline check at97–98 similarly loses its handle.

The Unknown classification is correct; loss of the available cleanup authority is not. Separate safe, correlated recovery-handle retention from full connection admission. Preserve only validated cleanup/receipt authority and conservative bounds; normal calls must remain disabled and reconnect must not silently discard the outstanding allocation. Do not salvage arbitrary unparsed bytes or trust a wrong-correlation response. If no trustworthy handle can be extracted, report that limitation honestly rather than claiming retained cleanup access.

Required authored control: a typed/correlated valid handle with over-request negotiated limits returns Unknown/Partial, leaves normal calls disabled, exposes bounded recovery authority, and refuses a second connection on that instance. Include the decoded-but-late reply case. These controls were not executed.

### P1-02 — retained cleanup-only handle inherits the invalid reply budget and cannot send disconnect

`client_v1.spl:76–83,151–160,227–237`.

A Connection advertising discovery.max_reply_bytes=2048 is structurally valid under `validation_v1.spl:48–53` (allowed1..1048576), and can pass response correlation when the caller requested4096. Connect stores it, then correctly rejects full admission and sets cleanup_only at155–160 because the transport requires at least4096. However, disconnect calls exchange, which selects the rejected2048 value from the stored connection at80. Line82 rejects it before submission. Every cleanup attempt therefore returns local NotApplied, although connect advertised cleanup_pending and retained the handle specifically for cleanup.

Keep a bounded recovery transport budget derived from the validated original request/configuration separately from rejected negotiated connection metadata. It must permit only cleanup/receipt operations and must not establish normal capability admission. A rejected peer limit must not make explicitly retained cleanup authority unusable.

Required authored control: a correctly correlated Connection with valid handle/lease and max_reply_bytes=2048 reports partial/unknown admission; an explicit disconnect can reach the transport using the safe recovery budget while queries/mutations remain denied. Assert that local limit validation does not short-circuit cleanup. Not executed.

## Source observations outside the findings

The six CoreMuxV1 signatures and mutable `me` transport methods match the port. The configured generic public import reexports the internal selected owner; there is no app directory-selection shortcut. Configuration admits only explicit literal IPv4 loopback, bounded port/auth/frame, ExistingOnly and Smux. The constructor opens no connection, starts no server, creates no local registry, and fabricates no capability descriptor.

Transport preflights request/reply sizes, sends framed bytes in8192-byte partial-write chunks, bounds each read request, validates the received frame length before reading its body, and recalculates remaining time from one start timestamp. It attempts exactly one close after every acquired-stream Result path. Socket owner behavior and actual timing/close success remain unexecuted dependencies. Value copies of TcpStream are confined to synchronous borrowed-use helpers; only the acquisition owner's mutable stream closes, and no descriptor is stored in the client.

A write attempt marks submission uncertain even if native write reports failure. Response decoding, correlation mismatch and post-submission timeout remain Unknown rather than NotApplied. Peer-controlled failure detail is replaced with fixed text. No automatic mutation replay exists. RequestStatus does not renew; normal query/poll renewal starts at request start, checks that the prior interval has not expired, and does not use reply arrival as a fresh lifetime. Revocation disables normal authority. Disconnect success/uncertainty disables normal authority; only identical explicit disconnect replay and receipt-only recovery remain within a non-sliding bound. Copies are not represented as new server leases; actual server authentication remains required.

Client exchange uses the reviewed codec's encoded-overhead preflight for capture/events and the negotiated reply frame ceiling. This is a source integration observation, not an independent proof of all codec size/node/depth bounds or native allocation behavior.

## Disposition

P0: none identified. P1: two open admission-cleanup defects above. P2: none additionally identified in this bounded review. Focused specifications/manuals were still pending in the four-file freeze; no assertion of test completeness is made. Correct the two findings, freeze exact revised inputs and independently rereview that delta before source acceptance. Native route, lease timers, failure injection, framed partial I/O, endpoint/capability and N2 cleanup qualification remain NOT_RUN.

## Cycle2 focused rereview — current disposition

Input freeze: `build/review/coremux-sosix-client-source-freeze-v2.md`, at HEAD61e47484277f98437f1f5090c94fb343bf51b4bc. Associated authored spec/manual/design freeze: `build/review/coremux-wire-client-complete-freeze-v2.md`. Five production pins and six scoped companion pins were independently verified against actual bytes. No codec traversal was repeated.

| Path | v2 SHA256 |
|---|---|
| src/lib/nogc_sync_mut/sosix/mux.spl | e470ea103fcd43e06d902c9453d05df2907ee1c1edefe516438131e683b87d2a |
| src/lib/nogc_sync_mut/sosix/mux/admission_v1.spl | 646a2dde6a78d051806b19802a8b06d3a15947f10a37c37ccef6a354f627a027 |
| src/lib/nogc_sync_mut/sosix/mux/client_v1.spl | 673562f135d767d7eb8da8688369762e4330004f6ea666d413f3c28bef9e8b6a |
| src/lib/nogc_sync_mut/sosix/mux/config_v1.spl | ca4a29bf1114af76834b936be41deb6659fdab2668c16d4fa560bcafead5e8dc |
| src/lib/nogc_sync_mut/sosix/mux/transport_v1.spl | d300b4945c1027c20e50e1f31b91f30a91a688cc80d3376352f9f12006ddfde8 |
| test/01_unit/lib/nogc_sync_mut/sosix/mux_client_v1_spec.spl | 84a268ab4c0f541ffa7bbd431f090f8786a9e7a70a705c4742fec3db5fb17b30 |
| test/03_system/tools/coremux_sosix_endpoint_spec.spl | 0eb227bd70020f302faf15f25fa023b07a9be20759f3262d14678154486ad1ec |
| test/fixtures/coremux/wire_echo_child.spl | 8ed8f178e692f7dc4935ee95c3adb615fa83fc58fe2f76ec5d7f5de36a92df03 |
| doc/06_spec/01_unit/lib/nogc_sync_mut/sosix/mux_client_v1_spec.md | 8380952754fe5e0d19b7dcec22b10e178d28ca00bea56cdb9453056e0c81eba2 |
| doc/06_spec/03_system/tools/coremux_sosix_endpoint_spec.md | 5aed0994b6afeb2e0cd715df5c916e36053026f997cb41277dda1cbac7506b74 |
| doc/05_design/caret_mux_wire_sosix_v1.md | a9cb4dbe77ef0215ce6b0fa65108a9b779d661eecb459390998f62be14d12867 |

### Historical P1 closure

P1-01 is source-closed. `client_v1.spl:101–122` now computes and retains a recovery-only disposition immediately after correlated structural decoding and before late or semantic rejection. `admission_v1.spl:24–37` requires the original validated Smux/ExistingOnly request, matching namespace/backend, valid snapshot/handle and lease terms. It computes conservative request-start bounds and retains a rejection instead of granting normal authority for late, over-request or below-wire-minimum negotiation. Unparsed, wrong-correlation, foreign and malformed candidates do not acquire cleanup authority. `connect:166–188` blocks a second connect for retained state or submitted uncertainty. Authority without an extractable trusted handle remains uncertain rather than fabricated.

P1-02 is source-closed. `config_v1.spl:31–40` selects Disconnect and RequestStatus reply limits from the retained original-request recovery ceiling, independently from the rejected peer limit. The actual exchange calls that selector at83. A peer2048-byte limit therefore cannot block cleanup through the previous minimum-frame check; normal calls remain denied by inactive lease authority. Recovery does not renew the lease or slide its existing retention interval. Production transport/export hashes are unchanged from v1.

The nine client controls call production config/deadline/admission/budget functions, including late and over-request rejection, exact original budget preservation,2048 recovery selection, foreign identities and Busy on a retained connection. The Busy fixture constructs bookkeeping explicitly and does not exercise a real network response; request encoding with a recovery budget is not proof that a native disconnect was sent. Those limits are accurately retained as NOT_RUN source coverage.

### Open P2-01 — endpoint PID oracle uses provider-dependent running-handle semantics

`test/03_system/tools/coremux_sosix_endpoint_spec.spl:5,78,89,122` imports `app.io.mod.process_is_alive`. That resolves through `src/app/io/process_env_ops.spl:43–46` to `process_is_running`, via the async compatibility reexport of the sync process owner. It is not the exact arbitrary-OS-PID presence seam. The Windows platform runtime at `src/runtime/platform/platform_win.h:798–805` casts the scalar to a HANDLE; the Rust owner at `src/compiler_rust/runtime/src/value/sffi/env_process.rs:1183–1193` searches only its local SPAWNED_CHILDREN map. Some standalone C owners accept OS PIDs, so behavior depends on the eventual linked provider. Here the real child is owned by a separate server process. A live reported PID can be rejected, and a false result after cleanup is not independent proof of absence under those other providers.

Use the already-approved generic `std.sosix.process.sosix_process_exists` alias of the arbitrary-PID owner. Document that this is OS presence, not exit-status proof, and retain actual linked-provider, PID reuse, retained-object and process-tree/Job qualification requirements. No new runtime ABI or shell fallback is needed.

### Open P2-02 — pending disconnect cleanup is discarded in successful workflow/teardown

`test/03_system/tools/coremux_sosix_endpoint_spec.spl:103,118` discards returned disconnect cleanup state. An Ok reply with cleanup.pending=true can pass through final child-absence checks to cleanup Ok(true), even though the provider explicitly reports unfinished lease cleanup. The first disconnect correctly checks pending at88; the second and cleanup-lease releases must do likewise. The auth scenario at155–156 should also require completed release if it reports the valid admission as cleaned up.

Bind these responses and reject pending cleanup before reporting success. Preserve the outer cleanup-before-assert structure and independent external guard; do not translate partial/unknown cleanup into absence. The external guard remains necessary for failures before owned IDs are known and for resources the test cannot independently reconcile.

### Endpoint evidence scope and final status

The three endpoint scenarios require an actual framed server, private auth, exclusive initially empty namespace, admitted echo child and coordinator-owned bound/unlistening port. Missing prerequisites fail explicitly; the absent-endpoint negative is not a provider PASS. Positive assertions use captured READY/ECHO content, reconnect token change, background survival and split geometry. Known session cleanup is attempted before the first scenario's assertions; uncertain creation/lease state remains an error requiring external cleanup. Manuals enumerate the actual cases/steps and clearly state authored/manual rather than executed/generated evidence.

Nonblocking coverage limit: the split scenario checks two pane records and rectangles, but does not independently establish the second child's readiness/liveness before teardown. Thus it is not yet complete execution evidence for both spawned children. No full Caret/IDE/Tmux suite or N2 soak is claimed.

Current source disposition: P0 none identified; production P1-01/P1-02 closed; endpoint P2-01/P2-02 open. Nine client plus three endpoint cases are authored, zero executed. Including the separate sixteen codec cases, the owner reports28 authored and0executed; this review does not independently admit the codec. No compiler/build/helper/product/native/SSpec launch, production edit or commit occurred. WARN/NOT_RUN remains; no old-server compatibility or runtime qualification is asserted.

## Cycle3 endpoint-only rereview — final scoped source disposition

Freeze: `build/review/coremux-endpoint-spec-freeze-v3.md`. All three actual pins matched; all19 production pins in the complete v2 freeze remained byte-identical. No production semantic rereview or runtime check was repeated.

| Path | v3 SHA256 |
|---|---|
| test/03_system/tools/coremux_sosix_endpoint_spec.spl | dc08d76018ccb64f64e2fdd45b8ffc5d273dcaf21e3708692a8b0cc5dcbdca45 |
| doc/06_spec/03_system/tools/coremux_sosix_endpoint_spec.md | 72514a691607c32716fdd6de483b9729f52c1df6cd006023b3f5cf808a540b39 |
| doc/05_design/caret_mux_wire_sosix_v1.md | c95a317b5371a7ef0d35c6ca8c353552250564e7283e769c3eaa66a738a659da |

P2-01 is source-closed: the spec imports the exact generic `sosix_process_exists` facade and uses it for reported external child PIDs before/after disconnect, across reconnect and after owned cleanup. Source/manual explicitly distinguish presence from PID incarnation, exit status and complete resource cleanup; actual linked-provider and external owner/Job/resource receipts remain mandatory.

P2-02 is source-closed: second-client disconnect at135–136, final cleanup release at151–152, unexpected auth issuance cleanup at188–192 and valid auth release at194–196 require cleanup.pending=false. Pending results remain failure before success assertions. The workflow still attempts owned cleanup before assertions and preserves uncertainty requiring the external guard.

The second-child coverage limitation is also addressed in authored source: split retains the original pane/PID, identifies exactly one distinct new pane and distinct present PID, captures that pane's own readiness, sends its own COREMUX_SPLIT_PING plus Enter and captures its echo. Reconnect verifies both pane/PID identities and both OS-presence observations. The first pane separately echoes its input after reconnect. These are meaningful intended oracles, not executed evidence.

Final scoped source findings: no remaining P0/P1/P2 identified. Historical v1/v2 findings/pins above remain intact. STATUS WARN/NOT_RUN:3 endpoint,9 client and separately reviewed16 codec cases total28 authored,0executed. No compiler/native/helper/product/test/docgen launch or commit occurred. Server route, actual provider/timing/failure behavior, complete cleanup, full Caret/IDE/Tmux coverage and N2 qualification remain unproved.
