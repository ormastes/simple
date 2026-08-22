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

---

## Follow-up 2026-08-22 (d) — the silent generic-argument drop, and the durable guard

Follow-up (c) recorded two items rather than fixing them. Both are closed here,
plus the enforcement it asked for.

### 1. Generic arguments were dropped by BOTH walks — a symmetric gap

(c) blamed the projection alone: "the scalar `type_name` branch calls
`lower_named_kind(type_name, [], span)` — it drops generic arguments". That is
true but only half the mechanism, and the missing half is why the probe read 0
errors. `materialize_imported_callable_type_dependencies_inner`
(`module_reexport_materialization.spl:916-947`) dispatches on the SAME scalar
capture:

```
for param in callable.params:
    if param.type_name != "":            <- "Dict" for Dict<text, MirType>
        ... materialize that ONE name
    elif param.array_element_name != "":
        ...
    else:
        for dependency in parser_type_named_dependencies(param.type_):   <- the walk that DOES recurse args
```

So for a scalar-captured generic the argument-recursing walk was **never
reached**. Materialization bound only `Dict`; projection then also projected
only `Dict`. Symmetric — hence no `unresolved type:`, hence 0 errors, hence the
(c) warning that 0 must not be read as "handled" was exactly right.

### The consequence, measured, not argued

`fn map_struct(d: Dict<text, MirType>)` imported across modules. The importer's
own symbol table records the callable's first parameter as — verbatim from the
new spec's probe of `symbols.get_symbol(lookup("map_struct")).type_`:

| | first param as recorded by the importer |
|---|---|
| pre-fix | `Dict<any,any>` |
| post-fix | `Dict<text,named>` (`named` = the real cross-module `MirType` symbol) |

`lower_named_kind("Dict", [], span)` hits its zero-argument recovery arm and
builds `Dict<any, any>`, so **both** the key and the cross-module value type are
erased. Every later phase that reads that signature — inference, MIR lowering,
layout — sees `any`. It is a silent type-fidelity loss with no diagnostic
anywhere, which is a worse failure mode than the array-of-tuple/pointer/union
arms fixed in (c): those at least errored.

The pre-fix negative control is the sharper evidence: with the owner's `use` line
**removed entirely**, the fixture still produced **zero** errors pre-fix. The drop
was swallowing the dependency outright, not merely under-resolving it.

### Fix

- `module_callable_types.spl` — new `imported_surface_projected_named_args`;
  both scalar branches (`imported_surface_type` and
  `imported_surface_type_projected`) now project each generic argument in the
  OWNER's qualified scope and carry them into `Named(sym, args)` /
  `lower_named_kind(name, args, span)`. The argument-less path is unchanged byte
  for byte, and `imported_surface_type_projected` consults the retained parser
  `Type` only when it still *is* the named type the scalar capture describes
  (`parser_type_kind_named_name(type_.kind) == type_name`), since `type_name`
  may have been captured before the Type crossed a nested boundary.
- `module_reexport_materialization.spl` — when the scalar shortcut is taken for
  a param or the return type, additionally run
  `parser_type_named_dependencies` over the retained Type. A superset of the
  scalar name and idempotent, so the fast path is preserved and only the dropped
  arguments are added.

### 2. `Weak` (`-T`) — fixed on the materialization side

`parser_type_named_dependencies` gained the `TypeKind.Weak` arm. Not fixed on the
projection side, deliberately and with a reason recorded in the allowlist below:
HIR has **no** `Weak` kind, so `lower_type` already erases `-T` to `Infer`
without erroring — there is nothing to project into, and inventing a mapping
would be the kind of unproven "fix" this lane already had to revert once.
Evidence of scope: owned `.spl` carries **zero** `-T` type positions (measured
2026-08-22; the only `: -X` grep hits are negative numeric literals in
`engine/render/camera.spl`). This closes a latent gap, not a live one.

### 3. The durable rule is now enforceable

`scripts/check/check-type-walk-constructor-parity.shs` (+
`scripts/check/type_walk_projection_allowlist.txt`) fails when
`parser_type_named_dependencies` handles a `TypeKind` constructor that
`imported_surface_type` neither handles nor allowlists **with a reason** — and
fails equally on a STALE allowlist line (a constructor listed as unprojected
that is now projected), because a list that no longer describes the tree is how
a ratchet silently stops ratcheting. Projection dispatches through accessor
helpers rather than naming constructors, so the marker→constructor map lives in
the script and a new projection arm must add its marker there. Verdict is the
last stdout line, same convention as the pre-push guards; a run that compared
fewer than 5 constructors is `ERROR — nothing was checked`, never a pass.
`--selftest` runs before every scan and is fatal (4 fixtures: a new unprojected
constructor must FAIL naming it; the same constructor allowlisted must PASS; an
allowlisted-but-projected constructor must FAIL as stale; an extractor that
matches nothing must ERROR with exit 2).

Measured: `PASS — 12 constructor(s) checked, 0 unprojected and unallowlisted`.
Allowlist holds 7 (`Function`, `Optional`, `Reference`, `Atomic`, `Isolated`,
`Projection`, `Weak`) — every one of them probed at 0 errors in (c), recorded
rather than silently tolerated.

### Reproduce spec

`test/01_unit/compiler/hir/imported_generic_argument_projection_spec.spl` —
measured **2 of 4 FAIL pre-fix, 4/4 PASS post-fix** (fresh worktree at
`624ee9947f6`, seed `/mnt/data/worktrees/goal-main-1/bin/simple`,
`SIMPLE_TIMEOUT_SECONDS=0`). It asserts the wrong OUTCOME (`Dict<any,any>` vs
`Dict<text,named>` as recorded in the importer's symbol table), not merely the
absence of an error, covers the return-type path as well as the parameter path,
and carries a guard-the-guard: with the owner's import stripped the same
signature must still fail, so the spec cannot go green because MirType started
resolving in the IMPORTER's scope.

### Pre-existing red, not introduced here

`test/01_unit/compiler/hir/imported_tuple_signature_dependency_spec.spl` is
`2 examples, 2 failures` at `624ee9947f6` **with and without** this lane's source
changes (measured both ways by stashing). Recorded rather than stepped over
silently; it is a separate defect from this one.
## Follow-up 2026-08-22 (e) — third mechanism: a GENERIC callable's signature was never projected at all

Two mechanisms are fixed above: owner-missing-import (`eeaf35d3be0`) and the
projection/materialization constructor asymmetry — array-of-tuple, pointer,
union (`4a40c00c8e5`, `9f11967564b`). This is the third, and it is neither.

### The bail

`declared_imported_surface_callable_type`
(`20.hir/hir_lowering/_Items/module_callable_types.spl`) opened with

```
if callable.type_params.len() > 0 or not callable.has_return_type:
    return nil
```

so a **generic** callable's signature was never projected. The importing module
still got a `SymbolKind.Function` entry — with a `nil` type. No parameter types,
no return type, and no projected identity for any cross-module type the
signature names. Its non-generic sibling in the same module projects fine.

The affected population is dominated by the generated fold visitors and codecs,
where *every* walker is generic:

```
fn walk_ast_asm_location<C>(node: AsmLocation, ctx: C, f: fn(AstWalkNode, C) -> C) -> C
```

### Measured, not asserted — including what the lead got WRONG

The lead for this lane predicted the bail also explained the run14 census names
dominated by those generated files (AsmLocation 30, AsmConstraintKind 30,
HirPattern 48, VhdlPortDirection 12, HirModule 12, HirExpr 12). **It does not,
and the measurement says so.** Five probes on the deployed seed
(`/mnt/data/worktrees/goal-main-1/bin/simple`, `SIMPLE_TIMEOUT_SECONDS=0`):

1. Synthetic generic callable, explicit owner import — 0 errors.
2. Same with the real `f: fn(AstWalkNode, C) -> C` parameter — 0 errors.
3. Same through a `export use`-re-export hop, glob owner import, glob consumer,
   and with the consumer actually CALLING the generic function — 0 errors.
4. Targeted lowering against the **real** `10.frontend/generated/ast_visitor.spl`
   and `10.frontend/parser_types_expr.spl` sources, with
   `SIMPLE_HIR_UNRESOLVED_TYPE_TRACE=1`: every `[ist-proj-miss]` /
   `[field-dep-unresolved]` line named `Span`, `bool`, `text`, `Option`, `i64`,
   `Node` — modules deliberately absent from the probe's closure. **Zero
   AsmLocation, zero AsmConstraintKind.**
5. All six owner modules that name the asm types in a signature
   (`hir_codec.spl`, `c_backend_translate_ops.spl`, `mir_to_llvm_helpers.spl`,
   `asm_constraints_helpers.spl`, `_CBackendTranslate/class_core.spl`,
   `mir_instruction_support.spl`) already import them explicitly.

So the bail does **not** emit `unresolved type` — a `nil` signature type is
silent by construction, which is exactly why this mechanism had no diagnostic
and was never counted. The run14 asm/HirPattern census names remain
**unexplained** by this lane and are NOT claimed as cleared here. Recording that
plainly rather than asserting a clearance is the whole point of the
"measure, do not reason" rule this record already carries twice.

### What this lane DOES fix, with a measured before/after

The defect is real and independently measurable: an imported generic callable's
symbol carries no type. Pinned by parameter count of the projected signature,
where `-1` means "nothing was projected":

| shape | pre-fix | post-fix |
|---|---|---|
| `walk_ast_asm_location<C>(node, ctx, f)` | **-1** (nil type) | 3 |
| non-generic sibling (control) | 2 | 2 |

### Fix

- `10.frontend/parser_types_expr.spl` — `parser_type_kind_is_function`,
  `parser_type_kind_function_params`, `parser_type_kind_function_return`,
  discriminant-guarded like every other `parser_type_kind_*` accessor.
- `module_callable_types.spl` — the guard is now `not has_return_type` only.
  `imported_surface_type` / `imported_surface_type_projected` take a
  `bound_type_params: [text]` list; a `Named` (or array-element, or scalar
  fast-path) name that the CALLABLE binds projects to
  `HirTypeKind.TypeParam(name, [])` instead of being looked up in the owner's
  qualified scope. That lookup is precisely what the old bail was avoiding: it
  would have traded a dropped signature for a bogus `unresolved type: C`.
- Same file — a `Function` arm on `imported_surface_type`, applying the durable
  lesson from follow-up (c). `fn(A, B) -> C` is in the MATERIALIZATION walk's
  constructor set and was not in the projection's; it only became *reachable*
  once generic callables were projected at all, and without it this change would
  have traded a dropped signature for a fresh `unresolved type: AstWalkNode` on
  every importer of a generated visitor.

Monomorphization is untouched — this is dependency PROJECTION, not
instantiation (hardening plan §9).

### Reproduce spec

`test/01_unit/compiler/hir/imported_generic_callable_signature_projection_spec.spl`
— **4 examples, 1 failure pre-fix** (`expected -1 to equal 3`), **0 failures
post-fix**. Carries the non-generic control (green both sides, proving the
defect is the generic guard and not the module shape) and an assertion that no
error names the callable's own type parameter `C`.

Pre-existing red, NOT caused by this lane and verified by `git stash` at
`624ee9947f6`: `imported_tuple_signature_dependency_spec.spl` is 2/2 RED on
origin/main.

### Follow-up (d) — MEASURED clearance (post19 vs run14), not predicted

Full stage-1 `native-build --source src/app --entry-closure`. **Both runs reached
`hir 688/688` and terminated `rc=1` at the same point**, so the two censuses are
directly comparable. Both columns counted on the same basis (`[hir-fatal]`
lines) — deliberately not mixed with the `error:` or anchored-`$` bases, which
give different totals for the same run.

| unresolved type | run14 (pre-fix) | post19 (post-fix) |
|---|---|---|
| **MirType** | **180** | **0** |
| **HirPattern** | **24** | **0** |
| AsmLocation | 15 | 15 |
| AsmConstraintKind | 15 | 15 |
| VhdlPortDirection | 6 | 6 |
| HirModule | 6 | **8** |
| **HirExpr** | **6** | **0** |
| HirFunction | 3 | 3 |
| CompiledModule | 3 | 1 |
| **total** | **258** | **48** (-81%) |

Poisoned modules: **56 -> 9** (-84%). None of the nine is a MirType victim; all
eight of the run14 MirType victims (`backend_port`, `bitfield`, `target_presets`,
`feature_caps_types`, `feature_caps_arch32`, `gpu_intrinsics`,
`spec_const_registry`, `portable_numeric_capabilities`) lowered clean.

**`HirModule` went UP, 6 -> 8.** Stated rather than buried: this is the
run14-hypothesis-(e) effect finally showing up for real — modules that were
previously poisoned before reaching that check now lower far enough to reach it.
It is a sign of progress, not a regression, but it does mean per-type totals are
NOT a monotone progress metric across runs and must not be read as one.

Scope note: post19 was built from the tree carrying ONLY the array-of-tuple fix.
The pointer/union arms landed afterwards and are NOT exercised by this
measurement; they were found by probe and have no instance in the run14 census.

### What is left, and it is NOT this mechanism

The survivors (AsmLocation 15, AsmConstraintKind 15, VhdlPortDirection 6,
HirModule 8, HirFunction 3, CompiledModule 1) are untouched by this lane,
consistent with the two OTHER mechanisms identified in follow-up (c):

- **Function-type params behind an early `nil`.** `declared_imported_surface_callable_type`
  returns `nil` when `callable.type_params.len() > 0`, so a generic callable's
  signature is never projected at all. The AsmLocation / AsmConstraintKind /
  HirPattern population lives in the generated visitor/codec files, e.g.
  `walk_ast_asm_location<C>(node: AsmLocation, ctx: C, f: fn(AstWalkNode, C) -> C) -> C`.
- **Generic arguments dropped by the scalar branch.** `CompiledModule` reaches
  importers as `Result<CraneliftCompiledModule, CodegenError>`.

Each needs its own lane, its own reproduce spec, and its own measured census —
not a predicate.
