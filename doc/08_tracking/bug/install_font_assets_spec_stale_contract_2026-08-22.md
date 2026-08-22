# Installer font-assets spec has stale source contracts

`test/01_unit/app/release/install_font_assets_spec.spl` successfully reads its
source fixtures through the canonical `read_file_text` facade, but currently
fails two unrelated assertions:

1. It requires `src/app/release/install.spl` to contain the obsolete raw call
   text `if not rt_file_write_text(wrapper_path, wrapper)`.
2. Its second example reports `semantic: variable PKG_DIR not found`.

These failures predate and are independent of removing the raw read export.
Update the spec to assert the safe facade contract and repair the fixture's
`PKG_DIR` binding before using it as release evidence. Do not restore raw SFFI
access to satisfy a source-string assertion.
