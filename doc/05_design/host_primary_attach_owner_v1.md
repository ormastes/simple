# Host primary attachment ownership

Status: source implementation, runtime qualification NOT_RUN. This is a
necessary Host foundation, not a completed Caret/container integration.

Previously the common primary attachment API had no production caller. Host
helper consumption and smux runtime binding supported output-follow only.
`host_primary_attach_open_v1` now composes a retained `HostLocalRootV1`, an
already admitted `HostHelperLeaseV1`, and the real common primary attachment
provider. Existing output-follow behavior is unchanged.

The new owner requires the enrolled Host capacity journal and actual retained
parent execution. It creates no authority, signer, service root, reservation,
or second scheduler. Helper prepare/begin still verifies signed grants and
approval through existing Host admission. Workload, helper, and broker budgets
remain charges against the existing physical-host capacity policy; this code
cannot impose a machine-wide limit on unrelated processes.

## Opening sequence

1. Validate the helper's executing journal row, retained request, prepared
   receipt, execution proof, expiry, and exact primary-plan admission.
2. Require the parent journal row to be executing. Resolve its retained request
   and actual provider observation through `host_local_resolve_execution_v2`.
3. Reproduce the primary plan with the actual common provider. Retain its
   returned owner even when planning fails. Require canonical equality with
   the admitted plan, including exact native identity and launch template.
4. Recheck helper authority correlations and exclusively publish the primary
   consumed record with readback and fsync before the native open.
5. Invoke `simple_container_open_primary_attach_v1`. Immediately retain the
   returned provider, session, and cleanup carrier before any archive work.
6. Correlate the session's native reference with the canonical broker's retained
   owner, or use the returned cleanup owner. Match the consumed template,
   generation, and deadline before recording native metadata.

`consumption_attempted` is historical, not proof of a complete durable write.
Partial publication and identical replay both require reconciliation; neither
permits another launch. Every error returns the original helper and current
Host root. After native opening, publication failures also return the live
session or cleanup carrier. No process PID is treated as workload identity.

## Evidence and domains

`host-helper-stream-primary-consumed` and `host-helper-stream-primary-native`
are separate archive categories within the existing protected journal. They
are evidence only. No codec reconstructs a live terminal session or transfer.
Output-follow retains its original schema and archive paths. The common
retained-helper correlation validator is shared; primary and output validators
independently bind their distinct plan digest through helper plan, reservation
intent, operation payload, and prepared receipt. One admitted helper therefore
cannot be spent across both plan domains.

The source specs cover strict record roundtrips and mutation refusal, domain
separation, and real-file identical/changed replay and partial-write refusal.
The existing primary plan spec also checks that the same helper admission
accepted for primary is refused for output-follow, and the inverse with a
properly rebound output-domain contract fixture. None was executed in this
change: the prior bootstrap/runtime campaign exhausted its six-cycle limit.
These specs do not prove native attachment, injected post-spawn failure
retention, Host settlement, performance, or cross-platform operation.

Owner opening is NOT_COVERED by these record specs. In particular, retained
parent resolution, provider replanning and owner retention on provider failure,
helper proof/receipt drift during IO, native spawn rejection/cleanup-required
results, session creation failure, and native-archive publication failure need
real Host/provider fixtures and execution. Eight record scenarios are not eight
owner-opening scenarios.

## Remaining integration

Primary cleanup/settlement now has a source implementation in
`host_primary_attach_settlement_v1.spl`, described in
`doc/05_design/host_primary_attach_settlement_v1.md`. It validates this distinct
consumption/native domain against canonical broker cleanup proof and uses the
existing Host journal settlement before releasing the helper charge. Runtime
qualification and positive native cleanup/settlement coverage remain pending.

smux now consumes this owner through an explicit V4 plan/bind/adoption and
cleanup/settlement lifecycle; see `doc/05_design/smux_primary_session_v4.md`.
That source integration is unqualified at runtime and exposes no interactive
input or geometry capability. Caret can migrate only after that composition
works end to end with independently authorized control ports.
The current Caret `--container` path is preserved and is not migrated here.
smux V3 replies require `outputMode = output-follow` and an exact output-only
capability shape. The separate V4 extension preserves those V3 semantics.

Windows Docker process primary attachment remains explicitly unavailable in
the common provider. Its actual attach broker loop, process ownership, and
input/resize lifecycle require implementation and native qualification before
the same Host primary opening surface can support it. No fallback is added.
