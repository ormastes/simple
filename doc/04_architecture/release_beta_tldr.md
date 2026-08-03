# Release Beta Architecture — TLDR

The beta is a two-stage, fail-closed evidence pipeline: required producer jobs
gate publication, then the completed GitHub run and published prerelease attest
final readiness.

## Core Shape

- A strict Stage 2→3→4 chain with stub fallback disabled produces the only CLI
  accepted for local tool and verification evidence.
- Seven selected non-macOS rows must produce executable archives; embedded
  revision/version/role manifests prevent source-only substitution.
- Full FreeBSD QEMU bootstrap, installers, full package, SimpleOS, installation,
  and whole tests are direct GitHub publication dependencies.
- A post-completion GitHub query binds the successful workflow and published
  prerelease tag into the final aggregate receipt.

## Operational Notes

- cache: reused only with provenance; a cache hit is never release evidence.
- perf/RSS: isolated Stage 3 ≤254 seconds; every strict stage ≤24 GiB max RSS.
- compiler: facade-glob cycles retain the shallowest per-root visit depth.

## Open Next

- [architecture](release_beta.md)
- [readiness checker](../../scripts/check/check-release-beta-readiness.shs)
- [release scenario](../../test/03_system/app/release/feature/release_beta_spec.spl)
