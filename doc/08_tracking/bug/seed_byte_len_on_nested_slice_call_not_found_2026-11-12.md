# Seed interpreter: `.byte_len()` on a nested call result fails

- **Status:** open
- **Found:** 2026-11-12, diag-P4 markdown lane
- **Component:** Rust seed interpreter (method dispatch on call-expression receivers)
- **Severity:** P3 (workaround: bind to a typed local first)

## Symptom
`text_line.slice(0, col).byte_len()` fails in the seed interpreter with
`method 'byte_len' not found on value of type str in nested call context`.
Binding first works:

```simple
val prefix: text = text_line.slice(0, col)
prefix.byte_len()
```

## Where worked around
- `src/lib/editor/services/md_diagnostics.spl` `_md_byte_col` (comment cites this)
- `src/app/md_lsp/md_lsp_handler.spl` `_md_lsp_line_candidates` (typed locals)

## Repro
```simple
val s = "café x"
print(s.slice(0, 4).byte_len())   # fails on seed; expected 5
```

## Related (different shapes, not this one)
- `seed_untyped_byte_len_binding_raw_i64_misdecoded_2026_11_09.md`
- `llvm_seed_text_byte_len_dispatch_2026-11-07.md`
