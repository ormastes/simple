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

## Trust, policy, and time owner checkpoint (2026-09-23)

`authority_owner.spl` now projects evidence signing roots only from the
loader's one-time immutable trust-root registry and pins its generation. It
owns the bounded receipt-age/challenge-TTL policy and samples the raw wall-clock
provider behind a typed negative-failure boundary with rollback quarantine.
The umbrella admission path uses those authoritative roots and time; its
legacy roots parameter is only an exact assertion and cannot select authority.
Partial initialization, root-generation change, clock failure, rollback, lock
failure, and unlock failure reject the operation.

This deliberately does not admit any release gate. Astra review found that the
loader's public first-writer initializer is not yet privileged, the legacy
verifier APIs still accept caller roots/timestamps, and performance campaign
policy remains caller-provided. Trust/policy/time therefore stay false and the
first blocker remains `trust-root-owner-unavailable`; crypto and serialization
also remain false. No caller-provided boolean or timestamp is promoted to
authority.

The owner keeps at most 16 copied 32-byte public keys and performs bounded
O(root-count) work only at initialization/root projection. Steady-state time
sampling is O(1), allocation-free apart from returned value construction, and
does not alter receipt signature verification or ledger hot loops.

TODO(environment): once an admitted Phase-2 test-capable runtime exists, run
`test/01_unit/os/services/evidence/authority_owner_spec.spl`,
`artifact_snapshot_spec.spl`, `verifier_owner_spec.spl`, and
`umbrella_admission_spec.spl`; then run SimpleOS QEMU root-absence,
root-replacement, clock-failure, and clock-rollback cases. Keep PASS blocked
until executable Ed25519 KAT/native constant-work evidence and authoritative
mutex concurrency evidence independently admit their remaining gates.
Before admitting trust/policy/time, route every exported verifier entrypoint
through this owner (or reject mismatched assertions), require a privileged boot
token for loader root initialization, move performance campaign policy out of
the copyable admission context, and add deterministic clock failure/rollback
and lock-failure injection coverage.

Static review is complete. Executable status remains unverified because only a
Stage-2 compile/native-build lane is admitted; it is not SSpec/test authority.
