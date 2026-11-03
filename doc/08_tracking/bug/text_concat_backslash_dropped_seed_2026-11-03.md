# Seed drops backslash in text concat

- **ID:** text_concat_backslash_dropped_seed_2026-11-03
- **Severity:** P2, open
- **Repro:** `bin/simple.exe test test/01_unit/compiler/50.mir/text_concat_backslash_spec.spl`
- **Observed (seed, interpreter):** `"x" + "\lld"` has len 4 ("xlld"-like, backslash lost); `"C:\dev" + "\simple"` has len 11, expected 13. Fails for const-folded and runtime operands.
- **Expected:** backslash escapes decode to one byte and survive concat.
- Spec is tagged @tag:in-development until fixed.
