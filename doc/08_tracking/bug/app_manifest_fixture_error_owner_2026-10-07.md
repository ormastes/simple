# App-manifest fixtures match a nonexistent error enum owner

Phase1 row23709 executed nine legacy backend-resolution cases: seven passed,
and both Electron-rejection cases failed with `missing return in non-unit
function _is_err_electron_not_available`. Both fixture copies import/type/
match ManifestError; actual src/os/desktop/app_manifest.spl declares
AppManifestError and returns Result<UiBackendKind, AppManifestError>.
Its Err(AppManifestError.ElectronNotAvailable) cannot match the fixture's
nonexistent ManifestError variant. The seven Ok paths do not enter that bad
nested match. No production backend-policy defect is established.

The repair replaces only the obsolete error owner name in each fixture's
import, type annotations, pattern and descriptive comment. All nine real
assertions remain; no wildcard true, error suppression or implementation
change is introduced. Local tracking search found no existing exact
manifest-helper error-owner diagnosis, so this dated record is separate.

Release base `7a88778fb9e2d07ddf9616aefcd152dffbdd46cc`.
Both exact changed-source hashes:
`8f832e34963c6787f6f3955108ccb9339c557cf5fde21947ff4c9b81634f5f03`.
API definition and original/changed patch proofs are pinned in
`/tmp/simple-app-manifest-error-fixture-fix-20261007/evidence`.
Original result `/tmp/simple-phase1-per-row-attempt-20261006/23709/result.json`;
original output `/tmp/simple-phase1-parallel-source-0/build/test-artifacts/unit/os/desktop/app_manifest_resolver/output.log`.

## Actual changed-copy evidence

- Legacy result `/tmp/simple-app-manifest-error-fixture-fix-20261007/build/test-artifacts/unit/os/desktop/app_manifest_resolver/result.json`:9/9, zero failures/skips,3996ms file duration (3999ms aggregate). Root observation `/tmp/simple-app-manifest-legacy-result-20261007`; kernel `/tmp/simple-app-manifest-legacy-kernel-20261007`, exit0/quiescent1.
- Canonical result `/tmp/simple-app-manifest-error-fixture-fix-20261007/build/test-artifacts/01_unit/os/desktop/app_manifest_resolver/result.json`:9/9, zero failures/skips,3699ms file duration (3701ms aggregate). Root observation `/tmp/simple-app-manifest-canonical-result-20261007`; kernel `/tmp/simple-app-manifest-canonical-kernel-20261007`, exit0/quiescent1.

Compiler SHA256 `0f9bfc1f7a9f6aca254755a543687d6b3d60f18b254da9441cb60e1cd3d4a2c7`;
frozen dependency source `e59027c353e9ed6ea8ddf572424da70e188fe511`.
These are scoped Phase1 diagnostic seed results, not native desktop/whole
bootstrap admission. No previously green criterion was replayed. Sidecar
review is N/A for this exact enum-owner synchronization. Token/cache/cohort
metrics are unavailable; none are guessed. The separate PBKDF2 missing
adapter record is an unresolved production task, not part of this fix's PASS.

## Manuals and scoped verification

Each copy's canonical SPL docgen ran once, generating one complete manual
with zero stubs. All nine executable scenario statement bodies match the
exact tested source. Reviewed factual headers state the host/backend matrix,
error-owner contract, recovery and diagnostic limits; generated bodies remain
unchanged beneath them. Receipts:
`/tmp/simple-app-manifest-{legacy,canonical}-docgen-20261007`, kernel exit0
and quiescent1 each.
Each single scoped scan reports CURRENT, score82, release_ready true and
blockers0; dimensions narrative80/structure60/oracle100/traceability80/
evidence100/coverage100/maintainability45. Receipts:
`/tmp/simple-app-manifest-{legacy,canonical}-scan-20261007`, kernel exit0
and quiescent1 each. Reviewed nonblocking warnings concern existing absence
of source STEP/REQ/design metadata, flat presentation, and heading-based
traceability/recovery recognition. Human-reviewed headers document those
facts without inventing requirements or editing already-passed test bodies.
Working/staged environment guards, layout zero and staged diff checks pass
for the explicit six-file test/docs scope, including the separate unresolved
PBKDF2 owner task. No passing test/docgen/scan was replayed.
