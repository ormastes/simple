# OpenType GPOS table parsed with the wrong tag

**Date:** 2026-07-16
**Status:** fixed / landed (`0cbe00d1eb8`)
**Severity:** P2 — GPOS (glyph positioning) table located by the wrong tag, so
positioning data was missed / mis-parsed.
**Component:** `src/lib/skia/feature/glyph/ot_parser_layout.spl` (OpenType layout
parser).

## Symptom

The OpenType layout parser looked up the glyph-positioning table under an
incorrect four-byte tag, so the real `GPOS` table was not found (or the wrong
table was read), dropping positioning/kerning data.

## Root cause

Wrong OpenType table-tag constant for GPOS in the layout parser. Fixed by using
the real OpenType `GPOS` tag.

## Fix

`0cbe00d1eb8` fix(font): use the real OpenType GPOS tag.

## Affected files

- `src/lib/skia/feature/glyph/ot_parser_layout.spl`
- `test/01_unit/lib/skia/ot_parser_spec.spl` (regression)
