# Local Windows RC1 artifacts

The user-selected `1.0.0-rc.1` profile requires native Windows x86_64 MSVC
Phase4/full bootstrap and the selected Windows whole-test evidence. Other
platforms remain visible as not executed or blocked and are RC2 work. The
canonical `release/support.sdn` policy selects required support. This preflight is not accepted
for any other version by `release windows-local-check`.

`release/support.sdn` is the exact support authority for this local
candidate. Its SHA256 must be supplied during candidate creation/admission and
must match the packaged `support.sdn`. Register the isolated release session,
freeze the candidate, build/package once, validate the genuine qualification
and trusted review/convergence receipts, then persist admission using the
existing release owner. No local preflight creates admission.

The selected compiler distribution has these ordered checksum roles:

1. `simple.exe`: the actual Windows Phase4 executable.
2. `simple-1.0.0-rc.1-x86_64-pc-windows-msvc.tar.gz`: the already-created distribution with the
   executable, required runtime dependencies/assets, license and third-party
   notices; payload validation belongs to qualification.
3. `simple.spdx.json`: the artifact's SBOM.
4. `support.sdn`: the exact canonical support policy.
5. `convergence.json`: reviewed protected-branch convergence evidence.
6. `release-notes.md`: Windows scope, deferred platforms and known limitations.

`artifacts.sha256` uses exactly these ordered names with lowercase SHA256,
two spaces and LF termination. These are compiler distribution roles. MCP/LSP
npm tarballs are explicitly outside this selected local profile; publishing
those packages requires their own admitted native builds and package evidence.

`qualification.json` is present alongside these assets and checked against its
separately admitted digest. It is not inside `artifacts.sha256`: the canonical
qualification receipt itself refers to that manifest's digest. Keeping these
identities separate avoids a circular checksum dependency.

Run `simple release windows-local-check` with the existing registered session
options and `--version=1.0.0-rc.1 --attempt=N --state-digest=SHA256
--target=x86_64-pc-windows-msvc --artifact-dir=PATH`. It validates persisted
admission, source HEAD, profile identity and the physical artifact checksums.
It neither builds/packages nor signs/publishes. It does not turn diagnostic
tests or a HelloWorld result into full release qualification.

Promotion must revalidate this preflight and use existing `promote-check` and
the exact admitted bytes. Signing authority must create one signed annotated
tag and push that one ref; tag/publication needs explicit authority. The legacy
tag-triggered multi-platform rebuild workflow is not the local promotion route.
No candidate, receipt or published version may be rewritten for recovery.

Packaging must use the existing tar and `scripts/check_release_payload.shs`
transport over a private staged payload; `src/app/release/package.spl` is a
legacy bootstrap packager and is unsuitable for this profile. Stage the exact
Phase4 `simple.exe`, the runtime libraries needed by native compilation, and
all non-system DLL dependencies from the qualified build evidence. Include
`LICENSE`, `THIRD_PARTY_NOTICES.md` and exact bundled fonts. Record each staged
input's hash and compare it after copying; validate the resulting archive with
`check_release_payload.shs --tar`. Package creation occurs before candidate
admission and is not promotion. The concrete package executor remains pending
the actual Phase4 dependency manifest; the checker alone does not complete RC1.
