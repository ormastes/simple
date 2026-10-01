# Native list comprehensions are not lowered

- Date: 2026-09-23
- Status: OPEN
- Lane: Rust seed HIR and pure Simple MIR; Phase2 full CLI native build

`src/app/devhub/version_manifest.spl` used a list comprehension directly as
the receiver of `.join("\n")`. In the Phase2 full CLI graph,
`Thread.join() -> i64?` was also registered. The Rust HIR lenient fallback
lowered the unsupported `Expr::ListComprehension` to `Nil` with type `ANY`.
The receiver-blind method-return suffix lookup then assigned the unrelated
optional return type to `.join`, rejecting the following string addition.
The focused failure is in
`build/mini_builds/phase2-424-repair/join-cycle2.log`.

This is more than a return-type collision. Rust HIR `lower_expr` has no
`Expr::ListComprehension` arm, and pure Simple MIR rejects
`HirExprKind.Comprehension` with `E-MIR-EXPR-Comprehension` in
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`. Assigning a string
type to the unsupported receiver would allow native code with wrong values.

The manifest renderer now constructs projection lines with a normal `for`
loop, then joins the resulting `[text]`. This preserves projection order,
spacing, and final newline. `test/01_unit/app/devhub/version_manifest_native.spl`
checks the complete rendered output. General native comprehension lowering,
including iteration, filter, and element typing, remains to be implemented
and tested in both compiler paths.
