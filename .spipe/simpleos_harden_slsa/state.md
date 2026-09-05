# Lane: SLSA provenance model (master plan §20/§21, companion to TUF §Phase5)

**Status:** Model landed, spec green. Pure-Simple, no real crypto/build.

## Scope

Exclusive paths (this lane only):
- `src/os/services/update/slsa_provenance.spl` (new)
- `test/01_unit/os/services/update/slsa_provenance_spec.spl` (new)
- `.spipe/simpleos_harden_slsa/state.md` (this file)

Read-only reference (not edited): `src/os/services/update/tuf_metadata.spl`,
`doc/02_requirements/feature/update_tuf_trust.md`,
`doc/01_research/domain/simpleos_production_host_master_plan.md` §20 (updates/
recovery — "TUF-style metadata for rollback/freeze defense, SLSA provenance
attestations") and §21.4 (evidence receipt model).

## What was modeled

A SLSA-style build-provenance attestation + verifier, deliberately compatible
with the existing TUF trust model rather than duplicating it:

- **`BuilderIdentity { id, trusted }`** — a build-service identity a
  provenance's `builder_id` can reference; `trusted` stands in for an
  out-of-band allow-list decision (mirrors how `tuf_metadata.spl` models
  signing keys as an already-verified id list, not real key material).
- **`Provenance { subject_name, subject_digest, builder_id, build_type,
  source_uri, source_digest, materials, slsa_level }`** — flattened shape of
  an in-toto/SLSA v1 provenance predicate. Attestation *signatures* are
  modeled as already verified (out of scope), same simplification the TUF
  model makes for `signatures_present`.
- **`ProvenanceOutcome { accepted, reason_code, reason }`** — bare struct
  outcome (not cross-module `Result`), matching `tuf_metadata.spl`'s
  `VerifyOutcome` shape.
- **`CombinedOutcome { accepted, reason }`** — the TUF+SLSA defense-in-depth
  gate result; `reason` names which side(s) rejected.

## Checks (in `verify_provenance` fail-closed order)

1. `verify_builder_trusted` — `builder_id` must resolve to a KNOWN and
   TRUSTED `BuilderIdentity`; unlisted or listed-but-revoked both deny.
   Reason: `SLSA_UNTRUSTED_BUILDER`.
2. `verify_subject_matches` — subject `name` AND `digest` must equal the
   artifact being installed; blocks an attestation-swap attack (a valid,
   trusted-builder attestation for a DIFFERENT artifact must not transfer).
   Reason: `SLSA_SUBJECT_MISMATCH`.
3. `verify_source_pinned` — `source_uri`/`source_digest` must both be
   non-empty; an unpinned build cannot back a supply-chain claim. Reason:
   `SLSA_UNPINNED_SOURCE`.
4. `verify_level` — `slsa_level >= required_level`; denies artifacts built
   below the caller's required provenance floor. Reason:
   `SLSA_LEVEL_TOO_LOW`.

Full pipeline: `verify_provenance(prov, artifact_name, artifact_digest,
trusted_builders, required_level) -> ProvenanceOutcome`, first-failing-check
wins (builder → subject → source → level), matching the TUF model's
first-failing-role-check pattern.

## Combined TUF + SLSA defense-in-depth gate

`verify_tuf_and_slsa(tuf_outcome: VerifyOutcome, slsa_outcome:
ProvenanceOutcome) -> CombinedOutcome` — imports `VerifyOutcome` directly
from `tuf_metadata.spl` (read-only import, no edits to that file) so the two
models compose without duplication. Accepts ONLY when both sides accept:

- TUF verifies WHAT is trusted: the signed metadata pointing at the artifact
  is authentic (root-trusted keys, threshold), fresh (not frozen/expired),
  and not a rollback.
- SLSA verifies HOW it was built: a trusted builder, from pinned source, at
  a sufficient provenance level, for exactly this artifact.
- A compromise that defeats only one model (stolen signing key that still
  can't fake a trusted builder id; rogue build system that still can't forge
  TUF metadata) is caught by the other. Tested all four quadrants:
  accept/accept, accept/reject, reject/accept, reject/reject — the reason
  string names whichever side(s) failed so neither is silently masked.

## Spec verdict

`test/01_unit/os/services/update/slsa_provenance_spec.spl` run via
`/tmp/slsalane/bin/slsajob run <spec>` (seed binary copied per lane test
recipe; deployed `bin/simple` was stale for this lane's new module):

```
9 examples, 0 failures   (SLSA verifier primitives)
1 example, 0 failures    (well-formed attestation — acceptance oracle)
4 examples, 0 failures   (gaps rejected — 4 distinct reason-code oracles)
4 examples, 0 failures   (combined TUF+SLSA gate — 4 quadrants)
```
Total: **18 examples, 0 failures.**

**Fault-injection proof (spec can fail):** temporarily forced
`verify_subject_matches` to always return `true` (attestation-swap attack
would then silently pass). Rerun caught it immediately:
- `verify_subject_matches rejects a digest for a different artifact` →
  `assert_false failed: got true`
- `rejects a subject digest mismatch (attestation-swap attack)` →
  `expected 0 to equal 2` (accepted instead of `SLSA_SUBJECT_MISMATCH`)

Reverted the fault, reran: back to 18/18 green. Oracle is real, not
tautological.

## Next increment (blocked)

- Real attestation-envelope signature verification (DSSE/in-toto) against a
  trusted attestor key set — blocked on the crypto stack (no real signing
  primitives landed yet in this repo's model layer).
- Build-time provenance emission — a real build step recording
  builder identity, source digest, and materials at build time — blocked on
  the build system integration (this lane is verifier-only, no build-time
  hook).
- Wire `verify_tuf_and_slsa` into an actual update-install call site once
  both TUF and SLSA move from model to real verification.
