# Spec-file helper with imported call inside block-if expression fails "semantic: value is not callable" under `simple test`

- Date: 2026-08-19
- Found while: adding text_layout unit specs (font_rasterizer_bitmap_spec)
- Binary: deployed seed `bin/simple` in /mnt/data/worktrees/render-harden
- Status: OPEN (workaround applied in the spec: inline the helper)

## Symptom

In a `*_spec.spl` run via `bin/simple test`, an `it` block that calls a
module-level helper A, where A calls module-level helper B, and B computes a
`val` from a multiline block-`if` expression whose taken arm calls an
IMPORTED function (`glyph_row_bits` from `std.common.ui.glyph_bitmap_5x7`),
fails at runtime with:

    semantic: value is not callable

The same import called directly from an `it` block works; a plain
helper-calls-helper chain with no imported call inside a block-if works
(both probed green). Renaming the helpers does not help. Inlining helper B
into helper A makes the spec pass, so the wiring `it -> A -> B(block-if with
imported call)` is the failing shape.

## Reproduce

Failing fixture (verbatim, fails 1/1 examples):

```spl
use std.spec.*
use std.common.ui.glyph_bitmap_5x7.{glyph_index_for_char_code, glyph_row_bits}

fn expected_on(codepoint: i32, row: i32, col: i32) -> bool:
    val gi = glyph_index_for_char_code(codepoint)
    val source_row = (row - 1) / 2
    val bits = if row > 0 and row < 15 and source_row < 7:
        glyph_row_bits(gi, source_row) << 2
    else:
        0
    (bits & (0x80 >> col)) != 0

fn count_on(codepoint: i32) -> i32:
    var n = 0
    var row = 0
    while row < 16:
        var col = 0
        while col < 8:
            if expected_on(codepoint, row, col):
                n = n + 1
            col = col + 1
        row = row + 1
    n

describe "probe helper chain with imported fns":
    it "counts ink":
        assert_true(count_on(65) > 0)
```

Passing neighbors (same session, same binary):
- local-only helper chain `it -> outer -> inner` (arithmetic only): PASS
- `it -> inner` and `it -> outer -> inner` where inner is a ONE-LINE wrapper
  around the same imported `glyph_row_bits`: PASS
- the same imported functions called from `bin/simple run` main: PASS

So the failure needs the block-`if` expression arm containing the imported
call inside the nested helper; not the import itself, not the nesting itself.

## Impact / workaround

Unit specs that factor per-pixel expectations into helpers hit this and
misreport as test failures. Workaround: inline the helper (done in
test/01_unit/lib/nogc_sync_mut/text_layout/font_rasterizer_bitmap_spec.spl,
which is now green 5/5 with identical logic inlined).
