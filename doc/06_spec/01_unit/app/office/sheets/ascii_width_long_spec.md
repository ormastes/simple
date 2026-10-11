# Spreadsheet ASCII width long controls

Purpose: preserve long output and byte counts for the UTF-8 cursor and builder.
Audience: engineers checking conversion correctness and scaling.
Requirement: REQ-SHEETS-ASCII-WIDTH-UTF8.
Executable: `test/01_unit/app/office/sheets/ascii_width_long_spec.spl`.

Each scenario repeats a five-character pattern 1,024 times and compares the complete
output to an independently specified pattern. ASC preserves long ASCII; JIS converts
long ASCII; ASC/JIS mixed Japanese, emoji, Latin-1 and NUL cases preserve every
unconverted codepoint. Both mixed cases also compare exact output byte length.

Four executed scenarios passed under the captured Phase 1 seed. Separate cold/warm
scaling and observed working-set evidence are recorded in
`doc/08_tracking/bug/2026-10-11_sheets_ascii_width_utf8.md`; these tests alone do not
prove a runtime SLA or qualify the full formula integration.
