<!-- codex-design -->
# Detail design: SFFI v2 admission acceptance

## Shared interface names

- `sffi_admission_acceptance_run(fixture_id: text) -> Result<text, text>`
- `sffi_admission_acceptance_summary(result: text) -> text`
- SSpec manual step: `step("Admit fixture <id>")`
- SSpec checker: `check_admission_category(result, expected)`

## Result model

The runner serializes only canonical categories:
`admitted`, `unsigned`, `artifact-mismatch`, `untrusted-signer`,
`abi-mismatch`, `stale-receipt`, `null-contract`, or `internal-error`.
`internal-error` is never accepted as the expected result for a negative
security fixture.

The verifier status file is an ephemeral typed decision channel, not signed
provider evidence. It is cleared before validation, may report why local
authentication could not begin (for example missing signature or untrusted
signer), and cannot substitute for the verifier-minted admission receipt.

## Hot-path design

The runner is maintenance/test-time only. Production admission caches typed
function slots after verification. No acceptance metadata or fixture lookup is
reachable from an admitted foreign call.

## Developing test policy

The initial executable SSpec carries `@tag("developing")`. It is fail-closed
until all fixture IDs have a real runner. The tag marks incomplete acceptance;
it is not a skip/pass mechanism.
