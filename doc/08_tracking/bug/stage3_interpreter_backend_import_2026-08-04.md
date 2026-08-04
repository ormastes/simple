# Stage 3 interpreter Backend import failure

## Status

Open bootstrap blocker discovered in the third and final permitted fix cycle
for the Clang 23.1 browser-demo migration lane on 2026-08-04. No fix was
attempted after the cycle cap was reached.

## Exact failure

Cycle 3 built and sanity-checked Stage 2, parsed all 543 Stage 3 closure files,
completed HIR/type checking, and passed the former `VhdlProcessKind`, `Symbol`,
and `Token` failures. Monomorphization then failed normally:

```text
phase3:hir_typecheck:done
phase4:monomorphize:start
[ERROR] phase 4 FAILED
error: in-process native-build: HIR lowering error in
src/compiler/backend/backend/interpreter.spl: unresolved type: Backend
```

Retained evidence:

- `build/bootstrap-clang-23-1-stage4-token-owner-cycle3.out`;
- `build/bootstrap/logs/aarch64-apple-darwin/stage3-native-build.log`;
- `build/bootstrap/bootstrap-progress.log` (`exit-1`).

## Ownership hypothesis

`compiler.backend.backend.interpreter` imports `backend_types.*` but uses the
`Backend` trait physically owned by `compiler.backend.backend.backend_api`.
The adjacent driver already imports that owner explicitly. A fresh scoped
session should confirm that direct owner import, add a regression, and start a
new bounded cycle; this session must not retry because its three-cycle cap is
exhausted.

