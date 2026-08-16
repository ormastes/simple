# Scheduler-owned actor channel authority system-test plan

Status: Modern SSpec source and authored mirror complete; native execution,
pure-Simple doc generation, and maintenance are blocked by the deployed
Stage-4 test ABI probe.

## Scope

This focused system test covers the implemented same-thread scalar-text actor
compatibility boundary: scheduler-owned registry/admission, finite mailbox and
reply credit, admission-time argument copying, copied-reference routing, and
unique terminal removal. It excludes synchronized cross-thread ingress, typed
heap/graph payloads, native C/interpreter parity, and provider-level stop/join.

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

## Traceability matrix

| Requirement | Test cases | Observable oracle | Coverage |
|---|---:|---|---|
| REQ-PAR-002 | primary | admitted reply retains `before` after caller mutates input | Partial: scalar-text copy only |
| REQ-PAR-006 | primary + unknown actor | one-slot mailbox/reply rejection; unknown registry rejection | Partial: same-thread actor surface |
| NFR-PAR-002 | primary | mailbox high-water=1, reply capacity=1, credit returns to zero | Partial boundedness |
| NFR-PAR-003 | primary + unknown actor | full, stopped, and unknown operations fail closed | Partial safe compatibility path |
| REQ-PAR-005/NFR-PAR-006 | 0 | exclusions retained | Missing from this focused spec |

## Typed evidence and manual policy

The primary scenario emits closed `actor-channel-authority/v1` evidence and
compares eight observed fields with independent `check_exact` literals. Missing,
extra, ambiguous, or mismatched fields fail. The primary five-step flow remains
visible; the unknown-actor case is folded as supporting error detail. The
manual must retain purpose, preconditions, workflow, failure diagnostics,
scorecard, provenance, and limitations.

## Ordered verification

Run each command once after a valid pure-Simple Stage-4 test surface exists:

```sh
SIMPLE_LIB=src bin/release/simple test test/03_system/feature/language/actor_channel_authority_spec.spl --mode=native
bin/release/simple spipe-docgen test/03_system/feature/language/actor_channel_authority_spec.spl --output doc/06_spec --no-index
bin/release/simple sspec-maintain scan test/03_system/feature/language/actor_channel_authority_spec.spl
```

Pass requires the native examples, zero docgen stubs, a current mirror, all
seven maintenance scores, blocker=0, and traceability PASS. The 2026-08-16
deployed Stage-4 attempt failed its bounded test ABI probe before scenario
execution. Do not substitute the Rust seed or hand-enter generated provenance.
