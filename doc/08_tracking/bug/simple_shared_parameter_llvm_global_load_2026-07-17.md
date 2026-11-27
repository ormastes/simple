# `shared` Parameter Lowers As Undeclared LLVM Global
## Resolved 2026-11-23 -- fixed in the Rust seed parser; regression tests added

## Symptom

During a full pure-Simple bootstrap, Stage 2 native-build failed for the HIP
and OpenCL backend contract modules with:

`llvm global load referenced undeclared symbol Shared`

Both failures used `shared` as a local and parameter name, then read fields
from that parameter. Renaming the binding to `contract` allowed compilation to
proceed (the in-tree HIP/OpenCL backends now use `contract`).

## Root cause

`shared` is a keyword token (`TokenKind::Shared`). In pattern position
(`val shared = ..`, `var`, tuple destructure, `match` capture, `Some(shared)`,
`for shared in ..`, `if val shared = ..`) `parser_patterns.rs` routes keyword
tokens through `parse_keyword_as_pattern("Shared")`, which takes the PascalCase
spelling used for enum variants (`Shared.X`, `Shared(..)`). When no variant
syntax followed, the plain-identifier fallback returned that PascalCase name
as the binding. The binding was therefore declared as `Shared`, the later read
`shared` (lowercase, via `parse_keyword_identifier("shared")`) matched nothing,
HIR lowering under lenient types turned it into `HirExprKind::Global`, and the
LLVM backend failed at `codegen/llvm/functions.rs` ("global load referenced
undeclared symbol"). Parameters were fixed separately (their path keeps the
source spelling).

## Fix (already on release/1.0.0)

`parse_keyword_as_pattern` now returns
`Pattern::Identifier(name.to_lowercase())` for the plain-identifier case, so the
binding keeps the real keyword spelling. Pinned at HIR level by
`hir/lower/tests/expression_tests.rs
shared_keyword_local_read_does_not_become_global_variant`.

## Regression coverage added with this update

`src/compiler_rust/parser/tests/shared_keyword_binding_names.rs` -- parses a
`shared` binding in eight positions and asserts the AST never contains
`"Shared"`. Verified: with the lowercase fix reverted, 7 of 8 fail (the lambda
parameter path never used the keyword-pattern route); with the fix, 8/8 pass
(`cargo test -p simple-parser --test shared_keyword_binding_names`).

## Not verified

The seed available on this host has no `llvm` cargo feature, so the original
Stage 2 LLVM native-build was not re-run end to end. HIP stage2 should be
retried with a `shared` binding restored if a doubt remains.
