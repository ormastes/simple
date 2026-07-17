# Release Font Asset Packaging Specification

> **Manual draft — pending canonical `spipe-docgen`.** This mirrors the
> executable SSpec while the pure-Simple runner is unavailable; it is not a
> generated PASS record.

Executable source:
`test/01_unit/app/release/install_font_assets_spec.spl`

## Preserve the installer-owned font tree

The source installer copies all 57 tracked files below `assets/fonts`, plus the
root license and third-party notices, into `share/simple`. Its launcher exports
that directory as `SIMPLE_ASSET_ROOT` before starting the runtime.

## Stage fonts in every host package

Portable bootstrap/full archives include the asset tree and use a launcher
beside `simple-runtime`. Unix packages stage fonts below
`/usr/local/share/simple` and export that root. Windows portable and NSIS
packages stage `assets/fonts` and set the installed package root. The executable
contract checks all three GC-mode package mirrors and rejects payload-only
staging that lacks a discoverable runtime asset root.

## Claim boundary

This source contract proves packaging paths and launcher policy. Native package
construction and installed-font loading remain pending the admitted pure-Simple
runner and platform packaging jobs.
