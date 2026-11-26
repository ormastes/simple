# Mail CLI host fixtures: helper step fails because no Phase 2 producer is configured (2026-11-26)

**Status:** worked around in CI (step skips with a notice); producer config still owner-owned.
**Workflow:** `.github/workflows/mail-cli-portability.yml`, jobs "Mail host fixtures (ubuntu/macos/windows)".

## Evidence

Run 45720130004 (`gh run view --log-failed`), identical on all three hosts:

```
MAIL_CI_PHASE2_PRODUCERS_JSON:
MAIL_CI_PHASE2_UNAVAILABLE: no existing producer is configured for <host>; set MAIL_CI_PHASE2_PRODUCERS_JSON with url, sha256, phase=2, format and compiler
##[error]Process completed with exit code 1.
```

Of the last 100 runs of this workflow: 31 failure, 3 success, 1 cancelled.

## Cause

The step "Prepare the real shared SDN configuration helper" reads the repository
variable `vars.MAIL_CI_PHASE2_PRODUCERS_JSON`. It is empty (no such variable is
set on the repo), so `scripts/ci/prepare_mail_config_helper.shs` refuses via
`refuse "no existing producer is configured for <host>"` and exits 1. This is a
missing producer configuration, not a code defect and not a missing secret.

## Change

The step still runs `--selftest` unconditionally. When the variable is empty it
emits a `::notice::` with the reason, writes `skipped=true` to `$GITHUB_OUTPUT`
and exits 0. The one step that needs `MAIL_CONFIG_BIN`
(`pop3_credentials_probe.shs all`) is gated on `steps.helper.outputs.skipped != 'true'`.
When the variable is set, the original command runs unchanged, so a bad or
host-missing producer entry still fails the job. Dialect validation, the
attachment probe and the Windows launcher probe do not use the helper and still run.

## Open

Owner: set `MAIL_CI_PHASE2_PRODUCERS_JSON` (url, sha256, phase=2, format,
compiler per host triple) to re-enable the shared-config scenarios. Until then they are not exercised in CI.
