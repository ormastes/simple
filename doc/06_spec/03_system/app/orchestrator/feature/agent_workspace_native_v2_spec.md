# Native workspace invocation V2

Status: **AUTHORED / NOT_RUN**, handwritten manual. The executable source is
`test/03_system/app/orchestrator/feature/agent_workspace_native_v2_spec.spl`.

Eight scenarios cover strict native packet round-trip; explicit full native manifest V2 wrapping the strict V1 base; mutual V1/V2 decoder rejection; explicit native
profile version and canonical field rejection; distinct V2 authority that rejects
unchanged V1 approvals; genuine test-key Ed25519 verification and altered model
rejection; and separation of invocation from signed workload cancellation.

The test policy and manifest are explicit DATA fixtures. Successful verification
is cryptographic contract evidence only if executed. It is not installed policy,
an actual source/opaque selection, a native capsule or an operational launch.
No positive native owner is fabricated. Compiler/runtime/native/SPipe/docgen and
coverage remain unexecuted/unmeasured.

Actual Host composition uses the existing progress registry and actual source,
lease and container facade. Its pending helper cancellation, source V2 opt-in,
native image/config gates, same-capsule launch, copied continuation fencing,
signed cancellation, lower retirement and Host helper-ACK cleanup require final
combined source review and actual-owner qualification. These contract scenarios
do not claim that coverage.

The seventh scenario checks executable size/ISA bounds and the exact complete
minimum calculation, including a 290 MB image with separate bootstrap/Git and
agent budgets. It does not turn a declared size or test-key signature into actual
source/capsule memory admission.

The eighth scenario uses a real admitted Host journal allocation with an inert,
explicitly scripted provider. A 1 GiB caller projection is rejected against the
actual smaller retained reservation before any provider command. This checks
allocation provenance without asserting a live native owner fixture.
