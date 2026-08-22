# HIR `unresolved type` / `unresolved name` blamed on innocent importers (stage-1 run13)

- **Filed:** 2026-08-22
- **Found by:** stage-1 run13 full-census build (worktree `stage1-clean15` @ `7f9a3e1c050`,
  log `scratchpad/fp11/stage1_build13.log`, census `error_census13.md`)
- **Status:** FIXED (source + diagnostics); verification build pending
- **Related:** `hir_enum_payload_blockvalue_unresolved_2026-08-21.md`,
  `hir_tuple_signature_dependency_unprojected_2026-08-21.md`,
  `duplicate_backend_types_terminal_declarations.md`

## Symptom

101+ modules `[hir-poisoned]` during step 2/6 of stage-1 run13, in three classes.

Class A — `HIR lowering error in <module>: unresolved type: <T>`, **338 occurrences**
across 14 compiler-internal type names:

| type | n | type | n |
|---|---|---|---|
| CodegenTarget | 113 | AsmLocation | 5 |
| MirType | 87 | AsmConstraintKind | 5 |
| BlockValue | 47 | HirModule | 2 |
| Export | 26 | HirFunction | 2 |
| TypeLayout | 18 | HirExpr | 2 |
| HirPattern | 14 | CompiledModule | 2 |
| HirIfArm | 11 | CompilationContext | 6 |

Class B — `unresolved name:` for `parser_type_kind_named_name` x10,
`parser_type_kind_array_element_name` x10 (module_surface_declarations.spl),
`expr_kind` x3 / `stmt_kind` x2 (desugar/suspension_analysis.spl).

Class C — `monomorphization is not implemented (Phase B)` x2. Pre-existing, filed
separately; not touched here.

## The census's "bare type-name fragments" were NOT errors

The census listed `text` 5061, `i64` 2873, `bool` 2204, `Option` 1988, `f64` 819,
`Any` 504, `char` 231, `Dict` 208 as suspected split-name or generic-argument
artifacts, and asked whether they were the non-injective-key bug of `5c38b388a53`.
They are neither. Grepping `unresolved type: X` matched the *body of an advisory
message*, not a diagnostic:

```
[hir-payload-origin-unresolved] owner=... payload=text: ... a later `unresolved type: text` will be reported ...
```

Anchoring the pattern to end-of-line (`unresolved type: [A-Za-z_]*$`) collapses
15,014 grep hits to **338 real errors**. The remaining 12,364 lines are the
advisory added by `hir_enum_payload_blockvalue_unresolved_2026-08-21.md`, and
**12,171 of them (98.4%) name a primitive**. Nothing is mis-parsed and no name is
split; the census's own regex was.

## Root causes

**A1 — payload half (BlockValue, 47 errors + 193 advisories).** A genuine source
defect. `src/compiler/10.frontend/parser_types_expr.spl:400` declares
`ExprKind.CustomBlock(text, BlockValue)`, and that module's ONLY import was
`Span`. `resolve_materialized_enum_payload_origin` asks the OWNER for a
declaration, a re-export hop, or an explicit import; all three missed, so the
origin came back not-found and the failure resurfaced as
`unresolved type: BlockValue` against importers that never name it. The advisory
landed exactly on target — `owner=compiler.frontend.parser_types_expr
payload=BlockValue`, the **only** non-primitive advisory in the whole run.

**A2 — callable half (the other 291 errors, 0 advisories).**
`materialize_imported_callable_explicit_dependency_inner` ends its sweep with a
bare `if selected_target < 0: return` — the exact silent-return shape the payload
path was fixed for on 2026-08-21, never applied to its twin. Twelve type names
were lost with **zero diagnostic naming the real owner**, which is why the class
looked like a resolver defect rather than the owner-side import gaps it is.

**B — two-hop plain glob.** `module_surface_declarations.spl` and
`desugar/suspension_analysis.spl` both do `use compiler.frontend.parser_types.*`,
and `parser_types.spl:11` does `use compiler.frontend.parser_types_expr.*`.
Neither hop is an `export use`, so the glob does not transit and the four
functions were never in scope.

## Fixes

1. `10.frontend/parser_types_expr.spl` — add `use compiler.blocks.blocks.value.{BlockValue}`.
   Arch-preserving: the frontend -> blocks.value edge already exists
   (`_FlatAstBridge/convert_nodes.spl:46`) and `blocks/value.spl` imports only
   `Span`, so no cycle and no new layer edge.
2. `20.hir/.../module_reexport_materialization.spl` — new
   `hir_dependency_is_builtin_type`, applied to the payload path and the
   callable explicit-dep wrapper. **Lowercase primitives plus `Any` only.** The
   capitalized dialect aliases (`Int`/`Bool`/`Char`/`String`/`Float`) and the
   container spellings (`Option`/`Result`/`Dict`/`Set`/`Map`/`List`/`Array`) are
   deliberately NOT filtered: `lower_named_kind` places their arms AFTER the
   symbol lookup precisely so a DECLARED type of the same name wins, and such
   declarations exist here (`struct Bool` in `*/ndarray/mod.spl`; 42 `Result`,
   14 `Option`, 10 `Array`, 7 `List`, 4 `Set`, 4 `Map`, 1 `Dict`). Filtering
   those would silently stop materializing a real user type — a correctness
   regression, not noise reduction.
3. Same file — replace the silent `selected_target < 0` return with a
   `[hir-callable-dep-origin-unresolved]` advisory naming owner and dependency.
   Advisory (`eprint`), not `self.error`, for the same reason as its payload
   twin: a consumer that already has the name in scope still lowers fine, so
   failing here would be a regression.
4. Explicit imports in `module_surface_declarations.spl` and
   `suspension_analysis.spl` rather than converting either glob hop to
   `export use` — that would widen two already-wide surfaces, and lint forbids
   `export use *`.

## Reproduce specs (all FAIL pre-fix)

- `test/01_unit/compiler/hir/enum_payload_owner_imports_dependency_spec.spl` (A1)
- `test/01_unit/compiler/hir/dependency_builtin_type_filter_spec.spl` (A2)
- `test/01_unit/compiler/hir/two_hop_glob_import_does_not_transit_spec.spl` (B)

Two of the three carry a guard-the-guard assertion (the payload use site still
exists; the `parser_types` hop is still a plain glob), so the pin cannot silently
pass if the shape it fences is refactored away.

## Expected clearance

| fix | errors cleared | advisory lines cleared |
|---|---|---|
| A1 BlockValue import | 47 of 338 | 193 |
| A2 builtin filter | 0 (noise/cost only) | ~10,200 |
| A2 advisory | 0 (names the 291 remaining owners) | — |
| B explicit imports | all 25 class-B | — |

The 291 remaining class-A errors are owner-side import gaps of the same shape as
A1; fix 3 is what makes them individually addressable — before it, the log named
only innocent importers. Do NOT close this record until a verification build
reports them by owner.
