# OCI request binding admission before CI entrypoint override

Status: planned source admission; no runtime qualification. Owner: Astra Podman,
worker: `/root/astra_podman/sol_podman_ci`, final source review: Astra Podman;
root coordinates release-line landing. Host and orchestrator owners agreed
existing contract names and provider ownership. No heavy build slot is held.

## Boundary and provenance

The starting point is release merge `e97e23b68b01d8c6e3634616d5fde7a1f1cbdf4d`.
Read the existing dirty `/home/yoon/dev/simple` implementation as identified
source material; do not copy the entire provider, host composition or unrelated
compiler/database edits. Existing command helper source SHA256 is
`ed48e7119a0aa5075d011f8772ecca0f88428d9860425594bf858cca1c2d8128`.
Record hashes of each additional admitted source in the final design report.

The release provider retains identity and phase but no payload. Its cached
`create` can report idempotent success for a changed request. Merely checking a
new `replace_entrypoint` boolean is insufficient: replay can turn the flag off.
The binding foundation must precede the new command mode.

## Minimum source closure

1. Existing `providers/linux/request_v1.spl`: `LinuxOciRequestV1`,
   `linux_oci_request_bounds_v1`, `linux_oci_request_digest_v1`. Preserve the
   versioned digest's field order, explicit counts and per-field hashes.
2. Existing `contracts/container/execution_options_v1.spl`: environment value
   type and request validation used by that exact digest. Admission of a request
   field does not authorize unsupported runtime effects.
3. Existing `contracts/container/bound_intent_v2.spl`: strict canonical SDN
   `RuntimeBoundIntentV2` encode/decode/match, composing existing immutable
   `RuntimeIntentV1` identity with the payload digest.
4. Surgical `oci_runtime_v1.spl` changes: re-export the extracted request;
   bounded in-memory bindings; preparation/create checks before cache reuse;
   create-owner lease; atomic writer recheck; read/save/current/recover binding;
   coherent eviction. Preserve existing native identity checks and cleanup.

5. Existing `providers/linux/request_codec_v1.spl`: canonical retained-request
   SDN encode/decode. Root approved this addition after the host owner identified
   the actual `host_linux_request_store_v1` consumer. Preserve digest field order
   and version defaults; roundtrip, tamper and unknown-field tests are required.

Existing SHA256, resource parsing, SDN encoding and digest validation
dependencies are reused. Decoded request bytes are data, not authorization.
The host persists the request before launch and compares its digest on reopen.

No attach, terminal, storage-observation or environmental execution code is
included. Nondefault unimplemented request fields fail explicitly at provider
validation; their presence in a digest must never become silent acceptance.
The CI command helper and additive override implementation stay parked until
the binding foundation is reviewed.

## Migration and effect rules

- New attempts bind the complete request before reuse and persist canonical V2
  before create effects. Same payload and operation replay normally; changed
  payload or explicit operation identity rejects before cache success/effects.
- Memory and disk bindings are both checked. Disk authority is reread under the
  stable owner/writer lease; stale memory cannot replace newer durable state.
- Legacy V1 has no proof of payload equivalence. It cannot authorize create,
  start or a new command mode. Return explicit unbound/unsupported information.
- Legacy exact-identity inspection, stop and destroy remain available for
  reconciliation. Do not rewrite a V1 record as V2 using an unproven caller
  payload. Preserve legacy writer/transition rules on that cleanup path.
- An unreadable, malformed, foreign-scope or ambiguous record cannot be treated
  as absent or overwritten. Unknown retention keeps host capacity charged.
- Bound V2 requests retain their binding through cleanup. Destruction does not
  erase the tombstone, permit resurrection or authorize global pruning.

The host owner confirmed this migration split and will not release capacity
from an unbound/blocked result. Actual host execution must retain full request
bytes/digest and plan before journal begin. No provider receipt implies a host
grant or a terminal stream lease.

## Required prevention evidence

Use real provider methods and typed exact-argv executor fixtures for source
regressions: identical prepare/create replay; changed command, args, flag,
image or resources before/after cached create; wrong operation; disk restart
with identical/mismatched payload; corrupt/noncanonical/foreign record; stale
writer and destroyed tombstone; bounded eviction; V1 create/start refusal and
V1 exact-identity inspect/stop/destroy without unsafe digest promotion.

The later command slice verifies literal argument vectors, args-only image
entrypoint inheritance, explicit executable override, NUL rejection, refused
ambiguous Podman JSON executable values, and actual CI request construction.
Do not claim full Kubernetes image-default equivalence or shell expansion.

Podman and the admitted self-hosted runtime are absent on this host. Specs and
manuals remain authored/unexecuted until the appropriate admitted toolchain and
real pinned-image fixture exist. Required compiler/lib/MCP checks, SPipe/docgen
and live container conformance must be reported as blocked, never passing.

## Worker source admission record (2026-11-07)

The command slice's five owned files and diff are parked under
`build/oci-request-binding/parked-command/`; provider/CI were restored before
foundation admission. Existing main source was preserved. Source SHA256 inputs:

- request_v1: `a97ab32dc5bac7da0e78083c084f9157d76e5c013bfb5a54935f084bad2437d3`
- execution_options_v1: `65f00098b9ac13105f9e0ddc7b85ef9b7b233375005e23fcd5ccc2d6f05c6a2a`
- bound_intent_v2: `b1eeb93709b3469c18057c7481967e87f822b0ba7231f28830640efa8083676f`
- request_codec_v1: `c4f747587f9da9fcf98e1c3ebd81ed7f13e445f9b08c597a5cf0224d735cb7a1`
- provider source material (surgical hunks only): `0f0a0d912b2f29193e2a929d3aa64635a6299433cdad940067899f5b3262145b`

Source details, migration limits, and authored/unexecuted evidence are recorded
in `doc/05_design/oci_request_binding_admission.md`. New provider fixture options
retain exact scripted effects while optionally exercising real owned journals;
production runtime selection is unchanged. No diagnostic runtime was invoked.

### Shared diagnostic source handoff

- Shared builtin-assert fixtures/checks:
  `test/fixtures/orchestration/oci_binding_admission_fixture.spl`.
- Tiny two-flow entrypoint:
  `test/fixtures/orchestration/oci_binding_admission_native_probe.spl`.
- Status: BLOCKED / UNEXECUTED; no build slot consumed. Supervising lane reported
  repeated `secure_memory.fill_span` failure in existing `afae` producer; SHA256
  reaches that same dependency, so the unchanged diagnostic build was not retried.
- Production provider remains frozen during this helper extraction. All 44 unit
  scenarios remain authored/unexecuted, with three matching authored manuals.
