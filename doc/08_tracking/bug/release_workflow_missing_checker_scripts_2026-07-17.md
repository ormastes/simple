# Release workflows reference missing checker scripts

- Date: 2026-07-17
- Status: resolved
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

## Resolution

The four workflow entrypoints are tracked again with current owners:

- executable roles use explicit byte budgets, including `simple-runtime`;
- directory/tar payloads require repository-identical notices and a complete,
  byte-identical tracked font tree when fonts are part of that package;
- SimpleOS smoke/full delegate to the canonical `simple os test --scenario`
  surface instead of a deleted QEMU tier script;
- MCP publish downloads the tagged Linux x64 bootstrap plus checksum, verifies
  it, and stages the package's exact native bin target.

Focused evidence:
`sh test/01_unit/scripts/release_checker_contract_test.shs` passes with tiny
local payload/release fixtures and a fake SimpleOS CLI. This does not replace
live QEMU or GitHub release evidence in their workflows.
