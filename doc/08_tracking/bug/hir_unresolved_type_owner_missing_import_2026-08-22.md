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

---

## Follow-up 2026-08-22 — the 291 owner-side gaps, enumerated and fixed

`1aa81cac8c6` closed the DIAGNOSTIC gap. This follow-up closes the SOURCE gaps it
made addressable.

### Method

Owner enumeration reproduces the compiler's own predicate from
`materialize_imported_callable_explicit_dependency_inner`: a module is an owner
gap for type `T` when `T` appears in a type position of one of its callable
signatures (or a struct field / `me` method), and the module neither **declares**
`T`, nor **explicitly imports** it, nor reaches it through a glob whose target
declares or `export use`-re-exports it (one hop — exactly what
`find_reexport_source` allows). Two modelling errors had to be corrected before
the list was trustworthy, and both inflate the count in the same direction:
multi-line `use x.{\n a,\n b\n}` blocks are real imports (a line-based reader
calls them gaps), and an enum VARIANT access `TopLevelItem.Export` is not a type
position. Fresh worktree at `1aa81cac8c6`, seed
`/mnt/data/worktrees/goal-main-1/bin/simple`, `SIMPLE_TIMEOUT_SECONDS=0`.

### Fixed — 49 explicit imports across 45 owner modules

| type | run13 errors | owner modules | import added |
|---|---|---|---|
| CodegenTarget | 113 | 2 | `compiler.backend.backend.backend_types.{CodegenTarget}` |
| MirType | 87 | 36 | `compiler.mir.mir_types.{MirType}` |
| Export | 26 | 1 | `compiler.frontend.parser_types.{Export}` |
| TypeLayout | 18 | 1 | `compiler.types.type_layout.{TypeLayout}` |
| HirIfArm | 11 | 1 | `compiler.hir.hir_definitions.{HirIfArm}` |
| CompilationContext | 6 | 1 | `compiler.common.compilation_context.{CompilationContext}` |
| AsmLocation | 5 | 3 | `compiler.frontend.parser_types_expr.{AsmLocation}` |
| AsmConstraintKind | 5 | 2 | `compiler.frontend.parser_types_expr.{AsmConstraintKind}` |
| HirModule | 2 | 1 | `compiler.hir.hir_types.{HirModule}` |
| HirExpr | 2 | 1 | `compiler.hir.hir_definitions.{HirExpr}` |

**273 of the 291.** Every edge is downward or intra-layer and already exists in
the tree: 60/70/90 -> 50.mir, 35 -> 30/20, 40 -> 00.common, 20.hir -> 10.frontend
(`hir_lowering/module_surface_declarations.spl`), 70.backend -> 10.frontend
(`hir_definitions.spl:22` already imports the same two asm types). No new
cross-layer edge, no glob widened, no `export use` added, no diagnostic silenced.

### NOT fixed, and why

- **HirFunction (2).** The only candidate is `20.hir/hir_types.spl:29`
  (`functions: Dict<SymbolId, HirFunction>`), whose provider is its sibling
  `hir_definitions.spl` — which already does `use compiler.hir.hir_types.*`
  (line 9). Adding the import would create a module CYCLE. This one needs the
  declaration moved, not an import; deliberately left for a structural change.
  (`85.mdsoc/.../app/__init__.spl` also names HirFunction, but that is the
  *different* `app/hir_function.spl` type re-exported from a sibling — correct
  as it stands, and importing 20.hir's HirFunction there would be a real bug.)
- **HirPattern (14), CompiledModule (2).** No owner gap exists under the
  predicate above: `35.semantics/enum_contract/hir_match_coverage.spl` does
  import `HirPattern` (multi-line brace block), and
  `70.backend/backend/__init__.spl` re-exports `CompiledModule` from its sibling
  `backend_types.spl`. These 16 need the run-time
  `[hir-callable-dep-origin-unresolved]` line from a real stage-1 build to name
  their owner; they are a different sub-shape (probably a re-export hop that the
  materializer does not follow), not a missing `use`.

### Reproduce spec

`test/01_unit/compiler/hir/callable_signature_owner_imports_dependency_spec.spl`
— measured **4/4 FAIL pre-fix, 4/4 PASS post-fix**. Covers the two largest
sub-groups (CodegenTarget 113, MirType 87 — the latter with one representative
per layer) plus the asm and HIR/layout groups, and carries a guard-the-guard
assertion that the fenced signatures still name the type.

### Authoritative terminal counts (run13 final dump, `error_census13.md`, 590 errors / 173 files)

The in-flight numbers used above are superseded. Terminal `unresolved type` = **479**
across exactly the same 14 compiler-internal names; the primitives appear ONLY in
in-flight `[hir-fatal]` traces and are absent from the terminal set. Mapped onto
the owner fixes:

| type | terminal n | owner modules fixed | status |
|---|---|---|---|
| MirType | 132 | 36 | cleared here |
| CodegenTarget | 122 | 2 | cleared here |
| BlockValue | 57 | 1 | cleared by `1aa81cac8c6` (A1) |
| Export | 35 | 1 | cleared here |
| TypeLayout | 34 | 1 | cleared here |
| HirIfArm | 25 | 1 | cleared here |
| HirPattern | 16 | 0 | **remains** — no owner gap under the predicate |
| CompilationContext | 14 | 1 | cleared here |
| AsmLocation | 14 | 3 | cleared here |
| AsmConstraintKind | 14 | 2 | cleared here |
| HirModule | 6 | 1 | cleared here |
| HirExpr | 6 | 1 | cleared here |
| HirFunction | 2 | 0 | **remains** — import would be a cycle |
| CompiledModule | 2 | 0 | **remains** — no owner gap under the predicate |

**402 of 479 cleared by this commit** (10 of the 14 names), **459 of 479 counting
A1's already-landed BlockValue** (11 of 14). **20 remain** across 3 names:
HirPattern 16, HirFunction 2, CompiledModule 2 — reasons unchanged from the
"NOT fixed" section above.

**Status:** class A callable half CLEARED for 459 of the 479 terminal
errors (402 by this commit + A1's 57); 20 remain (2 blocked on a cycle, 18
pending owner evidence from a verification build). Do not close.

## Follow-up 2026-08-22 (b) — why the predicted MirType clearance never happened

The owner-import lane (eeaf35d3be0 + 214fdfac2db) predicted that its 49 imports
across 45 owner modules would clear 402-459 occurrences **including MirType (87)
and AsmLocation/AsmConstraintKind**. Run14 measured `unresolved type` at **486**
vs run13's 479 — essentially unchanged — with MirType at **333** anchored
occurrences (153 in the `error:` census). That lane flagged its own figure as
predicate-derived and never observed in a build. It was wrong, and this is why.

### MirType is a DIFFERENT defect. The owner's import was never missing.

Ground truth came from a new level-gated probe, `[ist-proj-miss]`, added to
`imported_surface_type_projected` (default off, `SIMPLE_HIR_UNRESOLVED_TYPE_TRACE=1`),
run over a full stage-1 build. It names the OWNER whose qualified scope the
projection queried:

```
[ist-proj-miss] name=text owner=compiler.backend.backend.common.type_mapper lowering=src/compiler/backend/backend_port.spl
[hir-unresolved-type-origin] name=MirType lowering_module=src/compiler/backend/backend_port.spl span_file= span_line=0 span_col=0
```

The owner is **`70.backend/backend/common/type_mapper.spl`**, which imports
MirType explicitly on **line 8**. Nothing was missing from it. The signature is

```
fn map_struct(fields: [(text, MirType)]) -> text:
```

an ARRAY whose element is a TUPLE.

### Mechanism: the array arm projected by NAME, so array-of-tuple slipped past

`imported_surface_type` (`_Items/module_callable_types.spl`) handled exactly
three shapes: top-level `Named`, top-level `Tuple`, and `Array` — but the array
arm was keyed on `parser_type_kind_array_element_name`, which returns `""` for
BOTH "not an array" and "an array of something that is not a bare Named"
(`[(text, MirType)]`, `[[T]]`, `[T?]`). So `[(text, MirType)]` fell through to
`lower_type`, which resolves in the IMPORTER's scope, where the dependency is
bound only as `{owner}::{name}`.

This is the **same defect as the bare-tuple one fixed on 2026-08-21**
(`hir_tuple_signature_dependency_unprojected_2026-08-21.md`), one level of
nesting deeper: that lane taught the projection to recurse through a top-level
tuple, but left the array arm name-keyed, so wrapping the same tuple in `[...]`
slipped through again.

### Why NO diagnostic ever fired for MirType

`grep dependency=MirType` over run14's 6.3M-line `[ambig-dep]` trace returns
**zero** `[hir-callable-dep-origin-unresolved]`, zero `[hir-payload-origin-unresolved]`,
zero `sweep-verdict`, zero `router-step*-missed` — and for
`owner=compiler.backend.codegen` it shows MirType resolving **76/76**
(57 preresolved + 19 step1-bound). That is not a gap in the diagnostic: the
MATERIALIZATION walk (`parser_type_named_dependencies`) genuinely DOES recurse
`Array -> Tuple -> Named` and binds the name correctly. Only the PROJECTION
failed to consult it. **Materialization and projection walk the same type with
different recursion sets** — that asymmetry is the whole bug, and it is why an
owner-import predicate could never have predicted this population.

### Hypotheses tested and REJECTED (recorded so they are not re-tried)

- **Optional (`T?`) / generic-argument (`Dict<K, MirType>`) projection.** Fixed
  speculatively first; measured **byte-identical** results pre/post on a
  real-file harness (100 unresolved-type errors, same distribution). Reverted.
  Both are still unprojected shapes and may bite later, but they are NOT this
  population.
- **Errors reported against importers with the owner gap elsewhere (c).** Half
  true and misleading: attribution IS to the importer, but the owner has no gap.
- **MirType count GREW because more modules now lower far enough (e).** Not the
  cause; the shape was always broken.
- **Misattribution via accumulated diagnostics.** A real, separate bug found on
  the way: `driver_hir_pipeline_lowering.spl:438` passes the whole accumulated
  `bootstrap_lowering.errors` array to `driver_collect_hir_errors` on every
  module of the `sources<=0` loop, so that path re-reports modules 1..N under
  module N's name. The streaming path run14 used drains per module via
  `begin_module`, so it is NOT the MirType cause — filed separately rather than
  conflated.

### Fix

- `parser_types_expr.spl`: new `parser_type_kind_is_array`, because
  `..._array_element_name() == ""` cannot distinguish "not an array" from
  "array of a non-Named element".
- `module_callable_types.spl`: `imported_surface_type`'s array arm now recurses
  into the element via `imported_surface_type` when the element is not a bare
  Named type. Existing `[Named]` fast path unchanged.
- Two level-gated diagnostics kept (default off), so the next instance of this
  class is one run away instead of a day: `[ist-proj-miss]` (projection missed
  the owner's qualified scope) and `[field-dep-unresolved]` (the field-dependency
  path's silent four-step failure, which had no diagnostic at all — the twin of
  the callable path's).

### Reproduce spec (FAILS pre-fix)

`test/01_unit/compiler/hir/imported_array_of_tuple_signature_dependency_spec.spl`

Measured at `d684064754b` (pre-fix): `2 examples, 1 failure`,
`[array-tuple-dep-error] unresolved type: MirType`. Post-fix: `2 examples, 0 failures`.
The control (`[MirType]`, bare array) is GREEN on both sides, proving the defect
is SHAPE-specific rather than type-specific.

### Follow-up (c) — the general bug: materialization and projection recurse over DIFFERENT constructor sets

MirType was one instance. The generalisable defect is that the two walks over
the same parser `Type` handle different sets of `TypeKind` constructors.
Enumerated from the shipped source:

| walk | constructors handled |
|---|---|
| MATERIALIZATION `parser_type_named_dependencies` | Named (+ generic args), Tuple, Array, Function, Optional, Reference, Atomic, Isolated, Union, Projection, Pointer |
| PROJECTION `imported_surface_type` (before this lane) | Named (name only, **args dropped**), Tuple, Array (**by element NAME only**) |

Every constructor in the first row and not the second is a candidate for the
same failure. Probed each with the reproduce-spec shape rather than reasoning
about it. Result:

- **`*T` (Pointer)** — `fn f(x: *MirType)` → `unresolved type: MirType`. **LIVE**, 22 pointer params in owned `.spl`. **Fixed** in this lane.
- **`A | B` (Union)** — `fn f(x: MirType | text)` → `unresolved type: MirType`. **LIVE**, 13 union positions in owned `.spl`. **Fixed** in this lane.
- `T?` (Optional), `@T` (Atomic), `-T` (Weak), `[[T]]`, `[T?]`, `Dict<K, V>` — all measured **0 errors**. Not fixed, deliberately: an unproven "fix" here is exactly what this lane already had to revert once.
- **`Weak`** is missing from BOTH walks — a symmetric gap, so it does not produce this failure, but it means a `-T`-wrapped cross-module dependency is never materialised either. Recorded, not fixed.

Remaining known asymmetry, NOT fixed and NOT an error today: the scalar
`type_name` branch calls `lower_named_kind(type_name, [], span)` — it **drops
generic arguments**. `Dict<text, MirType>` projects as an argument-less `Dict`
rather than erroring, so it degrades type FIDELITY silently instead of failing
loudly. That is why the `Dict<text, MirType>` probe reads 0 errors above, and it
should not be mistaken for "handled".

The durable lesson for this class: **whenever a new constructor is added to
`parser_type_named_dependencies`, the projection must gain the matching arm in
the same change**, or a cross-module signature using it fails on an innocent
third party with no diagnostic naming the owner.
