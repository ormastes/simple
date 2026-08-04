# Stage 3 Symbol alias payload identity conflict

## Status

Resolved in source on 2026-08-04. Bootstrap cycles 2 and 3 passed this former
conflict and advanced to later monomorphization blockers. Full Stage 4 and
QEMU admission remain blocked separately.

## Exact failure

Fresh bootstrap cycle 1 built and sanity-checked Stage 2, parsed all 543 Stage
3 closure sources, completed HIR/type checking, and passed the former
`VhdlProcessKind` conflict. Monomorphization then failed normally:

```text
phase3:hir_typecheck:done
phase4:monomorphize:start
error: in-process native-build: HIR lowering error in
src/compiler/driver/driver_source_loading.spl: enum payload dependency
`Symbol` conflicts: `compiler.hir.hir_types::Symbol::struct` vs
`compiler.hir.hir_types::Symbol::type_alias`
```

Retained evidence:

- `build/bootstrap-clang-23-1-stage4-vhdl-owner-cycle1.out`;
- `build/bootstrap/logs/aarch64-apple-darwin/stage2-native-build.log`;
- `build/bootstrap/logs/aarch64-apple-darwin/stage3-native-build.log`;
- `build/bootstrap/bootstrap-progress.log` (`exit-1`).

## Ownership hypothesis

`compiler.hir.hir_types` declares `struct HirSymbol` and the compatibility
alias `type Symbol = HirSymbol`. HIR import lowering already projects that
alias to the concrete struct for field/method semantics, but materialized enum
payload collision identity still compares the alias spelling/kind against the
projected struct spelling/kind. The repair must preserve the public `Symbol`
alias while canonicalizing collision identity to its concrete terminal owner.
It must also replace staged-ABI-fragile `lookup(...).?` ownership checks on the
same import path with scalar `lookup_or_invalid` checks where required.

Required evidence is an exact focused alias-to-composite payload regression,
an adjacent non-alias collision control, and a fresh Stage 3 run reaching past
monomorphization before cycle 2 can be admitted.
