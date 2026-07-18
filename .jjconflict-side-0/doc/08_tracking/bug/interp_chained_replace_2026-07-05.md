---
id: interp_chained_replace_2026-07-05
status: RESOLVED (source and unit regression; deployed stage4 compatibility workarounds remain)
severity: medium
discovered: 2026-07-05
discovered_by: Manual testing in tools/pixel_compare/render_simple_html.spl development
related: tools/pixel_compare/render_simple_html.spl
related: src/lib/common/text/string.spl
---

# Interpreter fails on chained string method calls

## Resolution

The seed interpreter previously rejected chained calls to string methods such
as `s.replace(a, b).replace(c, d)` with:
```
semantic: method 'replace' not found ... in nested call context
```

Commit `050209d9b3` added `replace` and `replace_first` for temporary string
receivers to the shared value dispatcher. The existing parser preserves the
nested `MethodCall`, HIR assigns the inner `replace` result `TypeId::STRING`,
and the existing recursive evaluator routes that temporary text through the
dispatcher.

## Evidence

The focused regression is
`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`, which
applies a second `replace` directly to the first call's temporary result and
expects `HEllo`. Supporting source anchors are:

- `src/compiler_rust/test/unit/parser_tests.rs` — nested method-call parsing.
- `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs` — text result typing.
- `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs` — recursive
  temporary-receiver evaluation.
- `src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs` —
  shared `replace` dispatch and regression.

## Impact

The chained form is valid and no source-level workaround is required. Some
pure-Simple bootstrap code intentionally retains split statements for
compatibility with an older deployed stage4 executable; remove those only
after redeploy evidence.

## Scope

Seed interpreter `replace` on temporary string receivers. This resolution does
not claim general temporary-receiver method support: each receiver type and
method still needs an owned dispatch entry.
