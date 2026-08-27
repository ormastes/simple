# SFFI v2 admission acceptance — authored developing mirror

**Status:** DEVELOPING / fail-closed  
**Executable source:** `test/03_system/compiler/sffi_v2_admission_acceptance_spec.spl`  
**Doc generation:** BLOCKED — `bin/simple` is unavailable or non-executable in
the A1 worktree. This is an authored mirror, not generated execution evidence.

The executable SSpec uses repository test-discovery metadata
`# @tag developing` and calls the A2 test-time owner. It has no local
provider-admission implementation. The owner returns `Err` for unavailable or
unsupported fixtures; the blocked-result checker requires that exact `Err`, so
those cases never skip or masquerade as an admitted category.

## Frozen runner contract

- Runner: `sffi_admission_acceptance_run(fixture_id: text) -> Result<text, text>`
- Summary: `sffi_admission_acceptance_summary(result: text) -> text`
- Manual step: `step("Admit fixture <id>")`
- Checker: `check_admission_category(result, expected)`
- Fixture IDs and exact Ok categories: `admitted`, `unsigned`,
  `artifact-mismatch`, `untrusted-signer`, `abi-mismatch`, `stale-receipt`,
  and `null-contract`.

`Ok` is exactly the category; summary is that category unchanged, never receipt
or diagnostic prose. Unsupported/unimplemented fixture IDs return
`Err("blocked: ...")`, and the test fails closed. No `internal-error` fixture or
accepted category exists.

## Scenario matrix

| Requirement | Fixture ID | Required result |
|---|---|---|
| REQ-SFFI-ACC-001 | `admitted` | `Ok("admitted")` |
| REQ-SFFI-ACC-001 | `unsigned` | `Ok("unsigned")` |
| REQ-SFFI-ACC-001 | `artifact-mismatch` | `Ok("artifact-mismatch")` |
| REQ-SFFI-ACC-003 | `untrusted-signer` | `Ok("untrusted-signer")` |
| REQ-SFFI-ACC-003 | `abi-mismatch` | `Ok("abi-mismatch")` |
| REQ-SFFI-ACC-003 | `stale-receipt` | `Ok("stale-receipt")` |
| REQ-SFFI-ACC-003 | `null-contract` | `Ok("null-contract")` |
| REQ-SFFI-ACC-004 | `admitted` | exact canonical summary |
| NFR-SFFI-ACC-001 | `admitted` | A3 hot-path gate remains required |
| NFR-SFFI-ACC-003 | unsupported ID | exact `Err("blocked: ...")` assertion |

When the real runner lands, regenerate this mirror with `bin/simple
spipe-docgen test/03_system/compiler/sffi_v2_admission_acceptance_spec.spl
--output doc/06_spec --no-index`. This document is not provider-admission or
signature evidence.
