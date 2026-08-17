# Scheduler-owned actor channel authority system-test plan

Status: Modern SSpec source and authored mirror complete; native execution,
pure-Simple doc generation, and maintenance are blocked because the admitted
Stage-2 compiler has no qualified self-hosted test/docgen/maintenance surface.

## Scope

This focused system test covers the implemented same-thread scalar-text actor
compatibility boundary: scheduler-owned registry/admission, finite mailbox and
reply credit, admission-time argument copying, copied-reference routing,
unique terminal removal, and fail-closed query/reply lifecycle guards over
populated state. Owner-domain rejection uses deterministic identity-mismatch
injection; it excludes synchronized cross-thread ingress, typed heap/graph
payloads, native C/interpreter parity, and provider-level stop/join.

Executable:
`test/03_system/feature/language/actor_channel_authority_spec.spl`.

Authored mirror:
`doc/06_spec/03_system/feature/language/actor_channel_authority_spec.md`.

## Frozen primary flow

1. `Create one scheduler-owned bounded actor channel`
2. `Admit copied arguments through one actor reference`
3. `Observe finite mailbox and reply backpressure`
4. `Dispatch and consume the isolated result`
5. `Stop once through the owning scheduler`

Owner-domain flow:

1. `Seed reply actor pending-message and error state in the owner domain`
2. `Reject every query and reply lifecycle operation outside the owner domain`
3. `Restore owner authority and prove rejected access changed no retained state`

## Traceability matrix

| Requirement | Test cases | Observable oracle | Coverage |
|---|---:|---|---|
| REQ-PAR-002 | primary | admitted reply retains `before` after caller mutates input | Partial: scalar-text copy only |
| REQ-PAR-006 | primary + unknown actor + owner-domain | bounded/unknown admission rejection; every public query/reply lifecycle API hides seeded state off-domain | Partial: scalar compatibility surface; no synchronized ingress |
| NFR-PAR-002 | primary | mailbox high-water=1, reply capacity=1, credit returns to zero | Partial boundedness |
| NFR-PAR-003 | primary + unknown actor + owner-domain | full/stopped/unknown operations reject; off-domain sentinels hide state and restoration proves no mutation | Source-complete fail-closed scheduler boundary |
| REQ-PAR-005/NFR-PAR-006 | 0 | exclusions retained | Missing from this focused spec |

## Typed evidence and manual policy

The primary scenario emits closed `actor-channel-authority/v1` evidence and
compares eight observed fields with independent `check_exact` literals. The
owner-domain scenario emits closed `actor-owner-domain-rejection/v1` evidence
and compares ten hidden/restored observations. Missing, extra, ambiguous, or
mismatched fields fail. The primary five-step flow and owner-domain three-step
flow remain visible; the unknown-actor case is folded as supporting error
detail. The manual must retain purpose, preconditions, workflow, failure
diagnostics, scorecard, provenance, and limitations.

## Ordered verification

Run each command once after a qualified pure-Simple self-hosted test surface exists:

```sh
SIMPLE_LIB=src bin/release/simple test test/03_system/feature/language/actor_channel_authority_spec.spl --mode=native
bin/release/simple spipe-docgen test/03_system/feature/language/actor_channel_authority_spec.spl --output doc/06_spec --no-index
bin/release/simple sspec-maintain scan test/03_system/feature/language/actor_channel_authority_spec.spl
```

Pass requires the native examples, zero docgen stubs, a current mirror, all
seven maintenance scores, blocker=0, and traceability PASS. On 2026-08-16 the
admitted Stage-2 compiler exposed no qualified test/docgen/maintenance surface,
so no scenario executed. Do not substitute the Rust seed or hand-enter
generated provenance.
