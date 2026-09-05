# Lane UPD — TUF-style signed update metadata trust model

**Program:** SimpleOS production harden — master plan §20 (updates/recovery) + §22 Phase 5.
**Status:** Model complete, spec GREEN. Not committed (working copy only, per lane charter).

## What was delivered

- `src/os/services/update/tuf_metadata.spl` — pure-Simple TUF trust model + verifier.
- `doc/02_requirements/feature/update_tuf_trust.md` — roles, defenses, SLSA forward note.
- `test/01_unit/os/services/update/tuf_metadata_spec.spl` — 14 oracles.

## Four roles modeled

- **root** — trust anchor; owns signer keys + delegates keys to other roles.
- **targets** — vouches for artifacts (name/length/digest/version) via `TargetEntry`.
- **snapshot** — pins a consistent targets version (`recorded_targets_version`).
- **timestamp** — short-lived freshness pointer (freeze detection).

## Defenses modeled (verifier fns, `now` is a param — no clock call)

1. `verify_threshold` — >= threshold distinct authorized signers → else `TUF_BAD_THRESHOLD`.
2. `check_freshness(meta, now)` — deny if `now > expires_at` → `TUF_EXPIRED` (freeze).
3. `rollback_guard(current, incoming)` — deny if `incoming < current` → `TUF_ROLLBACK` (KEY property).
4. `verify_snapshot_consistency` — snapshot targets-version must match presented → `TUF_SNAPSHOT_MISMATCH`.
5. `keys_trusted_by_root` — every signature key must be in root trusted set → `TUF_UNTRUSTED_KEY`.
   `verify_update(root, timestamp, snapshot, targets, current, now)` runs all in order,
   fails closed with the first distinct reason; returns `VerifyOutcome{accepted, reason_code, reason}`
   (stands in for `Result<accepted, reason>` — bare struct avoids cross-module Result landmine).

## Modeled vs. real (explicit scope)

- NO real crypto: `signatures_present` is an already-verified key-id list, not signature checks.
- NO network pull, NO actual package install, NO clock (freshness takes `now` param).
- This is the trust-STRUCTURE verifier — the decision layer that resists repo/key compromise.

## Spec verdict

`/tmp/updlane/bin/updjob run test/01_unit/os/services/update/tuf_metadata_spec.spl`
→ **8 examples, 0 failures** (primitives) + **1 example, 0 failures** (accept) +
**5 examples, 0 failures** (attacks). Total 14, 0 failures.
Fail-once proven: disabling `rollback_guard` → rollback-attack oracle failed
("expected 0 to equal 4"), then restored to green.

## Next increment (resume plan)

Needs the crypto/signature stack:
1. Replace modeled `signatures_present` with real public-key signature verification
   over canonicalized metadata (crypto lib dependency).
2. Transactional A/B install: apply to inactive slot → health-check → atomic switch → rollback on fail.
3. SLSA provenance emission + verification: build artifacts carry verifiable provenance
   (builder id, source rev, build params), checked alongside targets metadata pre-install.
4. Key rotation + offline root ceremony modeling.

## Blockers

None for the model. Real-crypto/install increments blocked on the crypto/signature
stack + a transactional storage (A/B slot) owner — coordinate with those lanes.
