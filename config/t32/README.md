# TRACE32 Compatibility Assets

This directory contains repo-managed TRACE32 configuration files and container
helpers for the local `trace32_x11_container.Dockerfile` flow.

The current container path is headless and starts `t32mciserver`, not the older
X11 or Qt frontends. The repo therefore does not ship bundled TRACE32 GUI
compatibility shared libraries.

Licensing and provenance:

- do not assume vendor-installed TRACE32 runtime files under `/opt/t32` are
  covered by the repository root MIT license
- treat any local compatibility libraries added for experimentation as
  upstream-controlled third-party artifacts
- do not redistribute vendor runtime files or ad-hoc compatibility blobs as
  part of Simple release bundles unless their provenance and license terms have
  been independently validated

Release/archive policy:

- the GitHub release workflow excludes local development payloads and validates
  package contents before publish
- `.gitattributes` marks local development caches and compatibility blobs
  `export-ignore` so `git archive` does not include them
- `THIRD_PARTY_NOTICES.md` documents the intended bundled third-party surface
