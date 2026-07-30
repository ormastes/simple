# assets/ Manifest

Pinned, licence-attested binary assets consumed by evidence gates and by
SimpleOS image staging. These files are **tracked in git on purpose**:
there is no fetch step, submodule, or setup script that materializes
them, so a gate on a fresh clone can only find them here.

Removing entries below silently disables verification gates. The 2026-07-30
`chore: clean undeclared root artifacts` commit (`a4b4c008aff`) deleted the
whole `fonts/` tree as "undeclared", which broke 34 consumers (5
`scripts/check` gates, 2 `scripts/os` image-staging owners, 6 `src` paths,
21 test specs) until it was restored. This manifest exists so the tree is
declared and that judgement is not repeated.

## Allowed Entries

| Entry | Description |
|---|---|
| `FILE.md` | This manifest |
| `fonts/` | Pinned font bundle (see below) |

## fonts/

| Entry | Description |
|---|---|
| `cldr/` | CLDR release data (`release-48-2`: `LICENSE`, `RANKING.sdn`, `SOURCE.sdn`) consumed by locale/font ranking |
| `google-fonts/` | Licence-attested Google Fonts bundle |

### fonts/google-fonts/

| Entry | Description |
|---|---|
| `CORPUS.sdn` | Font corpus index |
| `apache/` | Apache-licensed families (e.g. `robotoslab`) |
| `ofl/` | SIL Open Font Licence families |

Each family directory holds its `.ttf` plus the `METADATA.pb` and
`OFL.txt` (or `LICENSE`) companions that carry its licence provenance.
`scripts/os/simpleos_font_bundle_companion.sha256` pins 35 of these
companion files by sha256, and
`scripts/check/check-linux-hosted-wm-live-window-evidence.shs` pins
`ofl/notosansmono/NotoSansMono[wdth,wght].ttf` by sha256
(`2cb2adb378a8f574213e23df697050b83c54c27df465a2015552740b2769a081`), so
the `.ttf` and its companions must be restored or removed together —
never a font without its licence file.

Consumers of record: `doc/03_plan/sys_test/simpleos_font_legal_bundle.md`,
`test/02_integration/os/port/simpleos_font_asset_staging_spec.spl`.
