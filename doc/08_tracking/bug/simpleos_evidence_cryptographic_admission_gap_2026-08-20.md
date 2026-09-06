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

Trust-root initialization is currently a structural first-writer mutex model,
not a privileged boot/configuration authority. Performance campaign policy is
also still supplied as copyable values, and freshness is caller-timestamped
rather than read from a canonical time owner. Their independent
`SIMPLEOS_EVIDENCE_TRUST_ROOT_OWNER_ADMITTED` and
`SIMPLEOS_EVIDENCE_POLICY_OWNER_ADMITTED` and
`SIMPLEOS_EVIDENCE_TIME_OWNER_ADMITTED` gates therefore remain false; merely enabling
crypto cannot accidentally make the structural model authoritative.

The ledger therefore rejects every `PASS` promotion; complete `BLOCKED` rows
remain usable.

Closure requires authoritative self-hosted concurrent execution evidence for
the mutex owner, a privileged immutable boot trust-root/configuration owner, a
service-owned performance campaign policy, plus executable Ed25519 KAT and native constant-work evidence over
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

Static review is complete. Executable status remains unverified because only a
Stage-2 compile/native-build lane is admitted; it is not SSpec/test authority.
