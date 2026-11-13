# Enum discriminant adapter: product code mutates an immutable array and a nil 'variants' access (2026-11-12)

Status: open
Area: src/compiler (enum discriminant folding adapter)

## Symptom

`test/02_integration/compiler/enum_discriminant_adapter_spec.spl` (15
examples, 6 failing under the seed on release/1.0.0). Two distinct product-side
defects:

1. "folds nested arithmetic before numbering the next implicit variant" and
   "preserves every supported operator through parsed declarations" fail with
   ```
   semantic: <spec>:154:35: cannot call mutating method 'push' on immutable
   array 'previous'
   ```
   The `previous` array lives in the adapter product code reached from the
   spec's call site; the seed rejects the mutation because the receiver is an
   immutable (`val`) array.

2. "detects a folded explicit value followed by an implicit collision" fails
   with
   ```
   semantic: undefined field 'variants': cannot access field on value of type 'nil'
   ```
   an adapter lookup returns `nil` where the spec (reasonably) expects an
   enum declaration record carrying a `variants` field.

## Root cause

The enum-discriminant adapter either declares a working array as immutable and
then pushes into it, or returns `nil` from a declaration accessor the
consumers treat as a populated record. The seed enforces array mutability
strictly, surfacing the latent bug; the `nil` access is a genuine product
robustness gap.

## Unblock

Make the adapter's accumulator array mutable (`var`) or use a builder, and
make the declaration accessor fail-closed (return the record or a named error,
never `nil`). Re-run this spec after the fix; keep the assertions as-is.

## FIXED 2026-11-13 (wave-2 deep-fix lane, work/compiler-seed-deepfix-20261113)

All 15 examples now pass under the tracked seed. Three distinct defects, two
of them beyond the record's diagnosis:

1. `push` on immutable `previous` — confirmed at
   `src/compiler/35.semantics/enum_contract/declaration_check.spl:146`
   (`val previous: [text] = seen_names[value]` then `previous.push(...)`).
   Fixed: `val` -> `var`. Cleared 4 examples.

2. nil `variants` — bisected with a scratch spec: the nil comes from the SPEC
   itself, not a product accessor. `parse_full_frontend` returns
   `ParserModule` whose `enums` field is `Dict<text, ParserEnum>`
   (`src/compiler/10.frontend/parser_types.spl:41`), and the spec indexed it
   positionally (`parsed.enums[0]`). Dict-miss-returns-nil is the DEFINED
   semantics on every engine (`doc/07_guide/language/dict_iteration_order.md`;
   pure-Simple lowering documents the same in
   `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:4592`), so no
   product accessor ever returned a record here — `parsed.enums[0]` was nil
   on every engine since the spec landed (dde012027fc, 2026-10-21). Deviation
   from "keep the assertions as-is": the receiver expression
   `parsed.enums[0]` -> `parsed.enums.values()[0]` (insertion-ordered Dict
   contract, single-enum fixture); every asserted value is unchanged.

3. NOT in the record — "distinguishes available noninteger literals" also
   failed: a float discriminant (`A = 1.25`) arrived as `HirExprKind.FloatLit`
   instead of the pinned `FloatLexeme`. Root cause:
   `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl` converted the
   enum discriminant WITHOUT the lexeme-preserving flag
   (`flat_bridge_lexeme_float_literals`), which only module-level const
   initializers and float match patterns set. Fixed by wrapping the
   discriminant conversion in that flag (third documented lexeme context).
   Without it, `hir_fold_literal_constant_v1` could not classify float
   discriminants as NonInteger through the lexeme form.
