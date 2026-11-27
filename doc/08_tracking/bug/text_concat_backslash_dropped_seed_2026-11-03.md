# Seed drops backslash in text concat -- INVALID

- **ID:** text_concat_backslash_dropped_seed_2026-11-03
- **Status:** invalid (premise was the escape sequence, not concat)
- Single-backslash literals are escape sequences and may drop the backslash by design. With escaped backslashes (two in source = one byte), const-folded and runtime concat keep it.
- Pinned as a passing regression: `bin/simple.exe test test/01_unit/compiler/50.mir/text_concat_backslash_spec.spl` (4/4 on the seed interpreter).
- A native/seed-compiled lane (native-build the spec) is not verified here.
