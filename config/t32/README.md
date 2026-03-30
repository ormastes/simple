# TRACE32 Compatibility Assets

This directory contains repo-managed TRACE32 configuration files plus two
legacy shared-library compatibility blobs used only by the local
`trace32_x11_container.Dockerfile` flow:

- `libXp.so.6`
- `libjpeg.so.62.0.0`

These files are not part of the intended Simple bootstrap/full release payloads.
They exist only to help an older local TRACE32 runtime start inside the Ubuntu
24.04-based container used for bring-up experiments.

Licensing and provenance:

- treat these shared libraries as upstream-controlled third-party artifacts
- do not assume they are covered by the repository root MIT license
- do not redistribute them as part of Simple release bundles unless their
  provenance and license terms have been independently validated

Release/archive policy:

- the GitHub release workflow excludes them indirectly by not packaging `config/`
- `.gitattributes` marks them `export-ignore` so `git archive` does not include them
- `THIRD_PARTY_NOTICES.md` lists them as development-only local artifacts
