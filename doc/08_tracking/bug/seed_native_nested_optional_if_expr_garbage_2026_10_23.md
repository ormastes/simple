# Seed-built Stage 2 SIGSEGVs on every `[]` literal: nested optional-valued if-expression miscompiled

Date: 2026-10-23
Lane: x86_64-unknown-linux-gnu, cranelift, trust-root Stage 2 sanity
Tree: release/1.0.0 @ a5aa33bc618 (CI run 39952380127; rejected Stage 2 binary taken from its
`bootstrap-failure-logs-Linux x86_64-cranelift-*` artifact)
Status: WORKAROUND landed at the HIR lowering site; the miscompile itself is OPEN.

## Symptom

After #4217 (codec fail-closed) the Stage 2 sanity probe
`src/compiler/bootstrap_admission/stage2_module_path_naming.spl` no longer crashes in the
HIR codec encoder; it now SIGSEGVs later:

```
#0 compiler.hir.generated.hir_visitor.walk_hir_type
#1 walk_hir_expr
#2 walk_hir_stmt
#3 walk_hir_block
#4 compiler.semantics.representation_boundary.unsafe_observations.representation_observe_function_v1
#5 representation_missing_manifest_observations_v1
#6 compiler.driver.hir_semantic_consumer_v1.collect_module_representation_receipt_v1
#7 compiler.driver.driver_hir_pipeline_passes.run_representation_manifest_pass
```

## Minimal reproducer (bisected from the 235-line fixture)

```simple
fn main():
    var out: [text] = []
```

`native-build --runtime-bundle core-c-bootstrap --entry-closure --entry <that file>` with the
Stage 2 candidate: `signal 11`. Same for `val out: [i64] = []`, `var out = []`, and
`fn f() -> [text]: []`. Non-empty literals (`["a"]`), `split`, `join`, loops and if/elif
do not crash. In the fixture, only the slice containing `var logical_parts: [text] = []`
crashes.

## Mechanism

`hir_lowering/_Expressions/expression_core.spl` `ExprKind.ArrayLit`:

- non-empty literal: `HirExprKind.ArrayLit(hir_elements, Some(homogeneous_element_type))`,
  passing a direct `Some(...)` -> fine;
- empty literal: `elem_type` was built by a nested optional-valued if-expression

  ```simple
  val elem_type: HirType? = if hir_elements.is_empty():
      if self.is_strict_empty_collections():
          self.error("...", e.span)
          nil
      else:
          Some(self.get_empty_array_default())
  else:
      nil
  ```

and the generated visitor walks that payload directly
(`generated/hir_visitor.spl:203`, `walk_hir_type(b_type_, ...)`). The Stage 2 binary is
seed-compiled, so the seed's native lowering of this form yields a garbage `HirType?`, and
the first walker that touches it faults. The bad node is also why every Stage 2 HIR blob in
that run decoded as `nil_in_non_optional_scalar` and was refused (cache-only, non-fatal).

## Workaround (landed)

The site now uses plain statements (`var elem_type: HirType? = nil` + assignment) under
`# @workaround bug=seed_native_nested_optional_if_expr_garbage_2026_10_23`. Same semantics.

## Open

- Reduce the miscompile to a seed-only fixture (an optional-valued `if` expression whose
  inner branch is a statement followed by `nil`, nested in an outer `if` expression) and fix
  the seed's native lowering. Then restore the expression form and drop the marker.
- Audit other `val x: T? = if ...: (stmt; nil) else: Some(...)` sites in `src/compiler` for
  the same shape.
- Verification of the workaround is a CI re-run of the x86_64 Stage 2 lane (host disk was
  read-only at the time, so no local Stage 2 rebuild).
