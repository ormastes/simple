# TRACE32 Compatibility Assets

This directory contains repo-managed TRACE32 configuration files and container
helpers for the local `trace32_x11_container.Dockerfile` flow.

The default container path is headless and starts `t32mciserver`. The repo also
supports an explicit GUI path through the same Docker/Podman wrapper using host
X11 forwarding (`DISPLAY`, `/tmp/.X11-unix`, and usually `XAUTHORITY`) via
`config/t32/trace32_x11_container.shs gui-on` or `scripts/t32q.shs gui-on`.

The repository does not ship bundled TRACE32 GUI compatibility shared
libraries; the GUI path relies on the locally installed vendor runtime under
`/opt/t32` plus host X11 access.

CLI actions are fail-closed: use `simple t32 action do <key> [arg] --confirm`.
The optional argument fills the named placeholder advertised by
`catalogs/actions.sdn`; missing or unused arguments are rejected before TRACE32
execution.

The container image registers `/opt/t32/fonts` with Fontconfig and enables the
distro's forced-bitmap rule because TRACE32 requests its vendor PCF faces
through Xft. After changing the vendor font directory or Dockerfile, rebuild
with `bash config/t32/trace32_x11_container.shs build`. A healthy image resolves the
startup face to a `t32` `PCF` file, not a TrueType fallback:

```sh
docker run --rm -v /opt/t32:/opt/t32:ro simple-trace32-x11:latest \
  fc-match -f '%{family}|%{style}|%{fontformat}|%{file}\n' \
  't32:style=lss:pixelsize=16:fontformat=PCF:antialias=false:hinting=false'
```

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
