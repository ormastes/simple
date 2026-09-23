# SimpleOS evidence cryptographic admission gap

Status: open, release-blocking for every capability-ledger `PASS`

`src/os/services/evidence/capability_ledger.spl` validates bounded receipt,
row, freshness, hash, performance, per-sample RSS, artifact-set, and nonce contracts. The new
`verifier_owner.spl` now owns trust roots, nonce history, generations,
challenges, verified handles, admitted-row expiry, and canonical-ledger state behind one private
canonical raw Mutex. No copyable public owner exists. Root initialization is
first-writer authoritative, nonce issuance is linearized, every table is
bounded, expired slots are deterministically reusable while nonce history is
retained. `artifact_snapshot.spl` independently re-hashes bounded source,
image, binary, configuration, fixture, and ordered artifact bytes. Handle
consumption and canonical-ledger publication are one transaction; all next
roots are built before assignment under the same critical section. Focused behavioral specs model conflicting initializer
and nonce contenders, copied generations, expiry/replay, and forged handles.

The cryptographic half remains deliberately disabled. The repaired common
pure-Simple Ed25519 path has strict decoding and constant-work window logic,
but still lacks authoritative self-hosted executable KAT/native proof. Candidate validation
may reach canonical unsigned bytes only after exact rehash, then stops at the
first unmet owner gate (`trust-root-owner-unavailable`) and never inserts a
verified handle. The cryptographic gate itself also remains false. A
caller can still construct `SimpleOsCapabilityAdmissionContextV1`, so its
booleans never authorize a promotion.

Challenge issuance is implemented in source behind the canonical mutex, but it
is structural behavior only—not release evidence—while
`SIMPLEOS_EVIDENCE_SERIALIZED_OWNER_ADMITTED` remains `false` pending an
authoritative self-hosted concurrent execution verdict.

Trust-root initialization is now boot-adapter-owned; the public compatibility
entrypoint is assertion-only and cannot become a structural first writer.
Performance policy is checked by an immutable service-local catalog and
freshness is sampled by the serialized authority clock. Their independent
`SIMPLEOS_EVIDENCE_TRUST_ROOT_OWNER_ADMITTED` and
`SIMPLEOS_EVIDENCE_POLICY_OWNER_ADMITTED` and
`SIMPLEOS_EVIDENCE_TIME_OWNER_ADMITTED` gates therefore remain false; merely enabling
crypto cannot accidentally make the structural model authoritative.

The ledger therefore rejects every `PASS` promotion; complete `BLOCKED` rows
remain usable.

Closure requires authoritative self-hosted concurrent execution evidence for
the mutex owner and executable Ed25519 KAT and native constant-work evidence over
`encode_simpleos_evidence_receipt_v1_signing_bytes`; authoritative capture-owner
delivery of the bounded byte snapshots and freshness time; plus concurrent
forgery, replay, key-revocation, failed-step, and restart tests.

Current focused implementation/evidence surfaces:

- `src/os/services/evidence/admission_gates.spl`
- `src/os/services/evidence/artifact_snapshot.spl`
- `src/os/services/evidence/signature_codec.spl`
- `src/os/services/evidence/ledger_transition.spl`
- `src/os/services/evidence/verifier_owner.spl`
- `test/01_unit/os/services/evidence/artifact_snapshot_spec.spl`
- `test/01_unit/os/services/evidence/verifier_owner_spec.spl`

## Trust, policy, and time owner checkpoint (2026-09-23)

`authority_owner.spl` now projects evidence signing roots only from the
loader's one-time immutable trust-root registry and pins its generation. It
owns the bounded receipt-age/challenge-TTL policy and samples the raw wall-clock
provider behind a typed negative-failure boundary with rollback quarantine.
The umbrella admission path uses those authoritative roots and time; its
legacy roots parameter is only an exact assertion and cannot select authority.
Partial initialization, root-generation change, clock failure, rollback, lock
failure, and unlock failure reject the operation.

This deliberately does not admit any release gate. The loader's package-owned
boot trust-root installation is privileged, while trust/policy/time stay false
and the first blocker remains `trust-root-owner-unavailable`; crypto and
serialization also remain false. The verifier now has root-free and time-free
authority entrypoints. Its legacy caller-root/time entrypoints remain
diagnostic: mismatched roots reject after authority startup, caller timestamps
reject once the verifier is authority-initialized, and a diagnostic
initialization cannot be upgraded to PASS authority.

The owner keeps at most 16 copied 32-byte public keys and performs bounded
O(root-count) work only at initialization/root projection. Steady-state time
sampling is O(1), allocation-free apart from returned value construction, and
does not alter receipt signature verification or ledger hot loops.

TODO(environment): once an admitted Phase-2 test-capable runtime exists, run
`test/01_unit/os/services/evidence/authority_owner_spec.spl`,
`artifact_snapshot_spec.spl`, `verifier_owner_spec.spl`, and
`verifier_authority_spec.spl`, `performance_policy_owner_spec.spl`, and
`umbrella_admission_spec.spl`; then run SimpleOS QEMU root-absence,
root-replacement, clock-failure, and clock-rollback cases. Keep PASS blocked
until executable Ed25519 KAT/native constant-work evidence and authoritative
mutex concurrency evidence independently admit their remaining gates.
Before admitting trust/policy/time, require a privileged boot token for loader
root initialization, preregister immutable performance campaign baselines,
and add deterministic clock failure/rollback and lock-failure injection
coverage.

This verifier wiring has source-level checks only. Executable status remains
unverified because only a Stage-2 compile/native-build lane is admitted; it is
not SSpec/test authority.

## Performance campaign policy checkpoint (2026-09-23)

`performance_policy_owner.spl` adds an immutable service-local campaign lookup.
Its authoritative API takes a candidate and the verified byte snapshot, never
the caller-constructible `SimpleOsCapabilityAdmissionContextV1`. The policy
value checker binds the exact row/workload, the indexed fixture artifact, a
distinct baseline identity, fixed config/board/CPU/frequency/noise/accelerator,
positive bounded RSS and baseline values, and the
canonical sample/noise/absolute-budget/regression projection. The immutable
catalog is empty because no reviewed fixture and baseline artifact set is
preregistered; a performance row therefore fails with
`performance-policy-unavailable`. This does not enable the policy gate.

The authoritative verifier now calls
`simpleos_evidence_performance_policy_check_v1(candidate, snapshot)` after
rehashing the snapshot and before creating a verified handle. The catalog is
immutable for the process lifetime, so the handle cannot outlive a policy
mutation. TODO(environment): preregister reviewed native campaign fixture and
baseline values only after an exact baseline artifact is available. Run the
focused policy and verifier authority specs with an admitted test-capable
self-hosted runtime and the native/QEMU campaign when the phase environment is
ready.
