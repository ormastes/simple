# Release workflows reference missing checker scripts

- Date: 2026-07-17
- Status: open
- Severity: P1 release pipeline failure

## Symptom

Release and publish workflows invoke checker paths that are not tracked:

- `scripts/check-executable-size-budgets.shs`
- `scripts/check_release_payload.shs`
- `scripts/check-simpleos-bootstrap-qemu.shs`
- `scripts/check-mcp-release-assets.shs`

The guarded `scripts/build-full.sh` path is also absent, so full releases always
use the fallback builder. The missing checks make the affected workflow steps
fail before they can validate packaged font assets or other release payloads.

## Required fix

Choose one canonical `scripts/check/` owner for each check, update every workflow
and executable spec to that path, and add a workflow contract that rejects any
referenced local script missing from the repository. Do not restore the deleted
historical scripts blindly: the old payload checker verified notices but did not
authenticate the bundled font tree, and the old SimpleOS wrapper depended on a
second missing QEMU script.
