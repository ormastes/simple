# Stage 3 HIR types unused parser import Token failure

## Status

Resolved in source on 2026-08-04. Bootstrap cycle 3 completed HIR and advanced
past this former `Token` error to the distinct `Backend` dependency blocker.
Full Stage 4 and QEMU admission remain blocked separately.

## Exact failure

Fresh bootstrap cycle 2 built and sanity-checked Stage 2, parsed all 543 Stage
3 closure sources, completed HIR/type checking, and passed the former
`VhdlProcessKind` and `Symbol` identity conflicts. Monomorphization then failed:

```text
phase4:monomorphize:start
error: in-process native-build: HIR lowering error in
src/compiler/hir/hir_types.spl: unresolved type: Token
```

Retained evidence:

- `build/bootstrap-clang-23-1-stage4-symbol-owner-cycle2.out`;
- `build/bootstrap/logs/aarch64-apple-darwin/stage3-native-build.log`;
- `build/bootstrap/bootstrap-progress.log` (`exit-1`).

## Ownership hypothesis

`compiler.hir.hir_types` imports the complete frontend `parser_types` and
`parser_types_expr` namespaces but uses no declarations from either module.
That accidental boundary causes the staged closure to lower `Parser`, whose
fields include the lexer-owned `Token`, even though HIR types do not consume
parser state. The narrow repair removes both unused wildcard imports and adds
a source-boundary regression. The physical parser owner also imports `Lexer`,
`Token`, `OutlineModule`, and `ParseError` directly from their acyclic owner
modules, preventing unqualified fallback from selecting one of several
unrelated `Token` declarations. Importing `Token` into HIR would preserve the
unwanted dependency and merely expose the next parser-only field type.
