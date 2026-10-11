# Windows SDK discovery exits on a trailing non-SDK directory

Status: candidate fix verified by focused checks and real host setup; no compiler
bootstrap or Phase4 qualification is implied.

On 2026-10-11, sourcing `scripts/setup/windows-msvc-bootstrap-env.shs` from
native Git Bash with `set -euo pipefail` and unset `WindowsSdkDir` /
`WindowsSDKVersion` exited 1 without diagnostics. The host's SDK Include tree
contained `10.0.22000.0`, `10.0.22621.0`, `10.0.26100.0`, then `wdf`.
The final directory has no `ucrt` child. The discovery loop's final
`[ -d .../ucrt ] && printf ...` therefore returned 1. With pipefail, the
command substitution failed even though an earlier valid SDK had been printed;
errexit stopped the caller before the subsequent empty-selection diagnostic.

The fix makes directory qualification an `if` statement. An irrelevant final
directory now contributes no output and no failure. The newest valid version
still wins; missing SDKs retain the explicit diagnostic, and failed pipeline
tools still fail rather than being masked with `|| true`.

Regression: `bash scripts/check/check-windows-msvc-sdk-discovery.shs` extracts
the production discovery block and launches it under errexit/nounset/pipefail.
Before the repair it exited 1 with `FAIL: trailing-wdf`. After the repair all
five cases passed: trailing `wdf`, numeric version ordering with an incomplete
newer version, empty Include, `wdf` only, and an injected sort failure retaining
exit 42. The complete real-host environment source then exited 0 and reached
the caller's completion marker. No compiler or runtime build was launched.

Reproduce host setup in native Git Bash:

```bash
set -euo pipefail
unset WindowsSdkDir WindowsSDKVersion
. scripts/setup/windows-msvc-bootstrap-env.shs
printf '%s\n' SETUP_COMPLETED
```

Evidence was collected in the isolated `D:/dev/simple-windows-contracts`
checkout. The frozen active bootstrap checkout was not changed.
