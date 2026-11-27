# Host Controller inspection continuation V3

Source: `test/01_unit/lib/nogc_sync_mut/orchestration/host_controller_inspection_session_v3_spec.spl`.
Status: **source-only NOT_RUN**. No actual Host/native inspection, Domain,
journal, process, cleanup or runtime/build result was produced. This is a new
lower continuation leaf in routing integration source cycle 2; it does not
change any immutable storage, protocol R1/R2 or held composition artifacts.

The sole production module is `host_controller_inspection_session_v3.spl`.
Its opaque in-process session stores operation ID, original execute-request
digest, the actual optional `HostControllerInspectionV3`, cached response/error
and cancellation flag. It stores no independent Domain or journal and has no
wire decoder, recovery factory or raw-observation authority constructor.

`host_controller_inspection_session_begin_v3(domain, operation_id, execute_request_digest)`
delegates once to the existing actual lower facade. Invalid IDs/digests are
refused before that call, returning the unchanged supplied Domain. The facade
checks the original retained execute packet, native store/lease/scope and actual
container owner. The wrapper does not duplicate those effects or admission.

`host_controller_inspection_session_step_v3(domain, session, cancel=false)`
delegates only the actual retained pending inspection to the existing step.
Cancellation remains sticky across later cleanup polls. Every returned Domain
and actual pending owner are retained before errors or encoding are inspected.
The caller must publish the returned Domain before interpreting the session.
Error/cancel never discards returned pending ownership or becomes success merely
because later polling drains it. Only an actual completed lower observation
passes through the existing `host_execution_observation_encode_v2` codec.

Completed sessions retain their response/error until the canonical app reads
and discards them. Calling step after completion returns the same session and
does not restart, reprobe or issue native recovery authority. The canonical app
must retain/replace the exact returned continuation; this wrapper does not claim
affinity against arbitrary trusted-source value copies.

Getters are `matches_v3(operation_id, execute_request_digest)`, `pending_v3`,
`response_v3`, `error_v3` and `exit_code_v3`. A normal pending continuation has
exit 0 with pending true; that is not completion. Any error/cancellation or an
empty unknown terminal result has exit 2. Matching cache metadata is not an
execution grant or native fact by itself.

| Authored pure metadata scenario | Assertions |
| --- | --- |
| Cache identity | Exact operation and original execute digest match; other/malformed identities do not. |
| Failure retention | Cached response plus absent pending inspection cannot erase a terminal error or produce zero exit. |
| Cancel/unknown | Cancellation or empty unknown terminal metadata stays nonzero without any fabricated owner. |

These terminal fixtures contain `inspection=nil`, no Domain/journal/native
store and no fake live inspection. They test metadata gates only; no actual
observation, native owner or probe success is inferred from their strings.

Production qualification procedures — **NOT_RUN**:

1. Obtain an actual admitted Windows Host service Domain and retained signed
   execute packet through the lead's existing producer/owner path. Invalid
   operation/digest input must return the original Domain and nonzero session
   without issuing a native inspection. Never fabricate a Domain for this test.
2. Begin once for a real retained execution, publish its returned Domain, then
   poll the same actual pending continuation. Verify the facade's exact native
   store, lease, scope and original execute-request digest checks. A mismatch
   must preserve every actual returned owner and remain a refusal.
3. Request cancellation during an actual pending native inspector. Publish each
   returned Domain before checking error; continue the returned pending cleanup
   until native release is confirmed. Cancellation/error remains nonzero after
   cleanup. Disconnect alone must not create a new cancellation or probe.
4. Obtain an actual completed observation and retain its exact encoded response.
   Poll/cancel the completed session again before canonical discard. The response
   stays cached, returned Domain is unchanged and real native launch/probe traces
   show no restart. Then the canonical app reads/discards it exactly once.
5. Cause a real native failure with pending cleanup where supported and verify
   that error/encoding failure never drops the pending carrier or actual Domain.
   Record native provenance and cleanup receipts; pure metadata tests cannot
   substitute for this evidence.
