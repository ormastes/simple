# Build workflow green status does not prove requested distribution artifacts

Status: open. Static review only; the workflow is owned by another active
session.

In `.github/workflows/build-binaries.yml` near lines 276–322, a failed
Windows Stage 2 build sets `produced=false`, then uploads a clearly named seed
fallback. A green workflow can therefore coexist with no Windows Stage 2
product. The Linux smoke path near lines 370–388 can also skip both execution
probes. These are useful diagnostics, but they are not a complete distributed
build qualification result.

## Required fix

Add a protected distribution acceptance checker for the requested target
matrix. It must require each target's native product provenance, exact artifact
identity and mandatory execution result; classify seed fallback and skipped
execution as `BLOCKED` for a Stage 2/dist-build PASS claim. Wire that checker
as the required workflow conclusion before accepting or reusing a signed
local build receipt. Preserve fallback artifacts for diagnosis under an
explicitly unqualified name.
