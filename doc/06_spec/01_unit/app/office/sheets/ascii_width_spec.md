# Spreadsheet ASCII width conversion

Purpose: verify ASC/JIS preserve UTF-8 while converting ASCII width.
Audience: engineers reviewing spreadsheet formula regressions.
Requirement: REQ-SHEETS-ASCII-WIDTH-UTF8.
Executable: `test/01_unit/app/office/sheets/ascii_width_spec.spl`.

| Scenario | Exact expected behavior |
|---|---|
| Full-width Latin letters | `ＡＢＣ` becomes `ABC` |
| Full-width space | `Ａ　Ｂ` becomes `A B` |
| Full-width digits | `１２３` becomes `123` |
| Mixed full-width text | `ＡＢＣ　１２３` becomes `ABC 123` |
| JIS Japanese pass-through | `日本語` is preserved |
| ASC supplementary characters | `Ａ日😀１` becomes `A日😀1` |
| JIS supplementary characters | `A日😀1` becomes `Ａ日😀１` |
| Embedded NUL | ASC preserves NUL and following Japanese text |
| JIS empty input | Empty output |
| ASC empty input | Empty output |

Unchanged release bodies fail eight scenarios. The final owner passes all ten
under the captured Phase 1 seed. Full formula integration remains baseline blocked;
see `doc/08_tracking/bug/2026-10-11_sheets_ascii_width_utf8.md` for provenance.
