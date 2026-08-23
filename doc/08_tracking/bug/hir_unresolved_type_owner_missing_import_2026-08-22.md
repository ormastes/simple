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
- `module_callable_types.spl` — in **`declared_imported_surface_callable_type`
  only** (`:360`, the IMPORTED-callable path), the guard is now
  `not has_return_type`.
  **A `type_params.len() > 0` bail deliberately STILL STANDS at `:143`, in the
  sibling `declared_surface_callable_type`** (`:142`), which types the module's
  OWN callables rather than imported ones and was never in this lane's scope.
  The guard is therefore NOT gone file-wide or tree-wide, and a future
  `grep 'type_params.len() > 0'` on this file will legitimately return both
  sites (plus a third, `fn_decl.type_params.len() > 0` at `:91`) — do not read
  those as an incomplete revert or an unapplied fix, and do not "finish the job"
  by removing them. Only the imported path was measured, and only it changed.
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

## Follow-up (f) — both generic lanes REVERTED after run15 (2026-08-22)

(Renumbered (e) -> (f) on re-land: two sections had independently been labelled (e).)

Follow-ups (d)'s two fixes, `d481f15e1ac` (generic arguments) and
`86787968989` (generic callables + the `Function` arm), were **reverted**. On a
full stage-1 build they took `[hir-fatal]` from post19's 48 to **3716** and
poisoned modules from 9 to **437**.

The mechanism is this record's OWN mechanism, reached from a new direction:
a projected generic argument is looked up with
`lookup_qualified_type_raw(imported_module_name, name)` where
`imported_module_name` is the module the importer NAMED — a package facade or
glob re-exporter — not the module that DECLARES the type. On the miss,
`imported_surface_type` falls to `lower_type` in the IMPORTER's scope and emits
a hard `unresolved type: X` against a module that never names X.
`50.mir/hwir/bit_vector_constant.spl` (no `use` line at all) reports exactly the
four `X?` optional fields that `50.mir/mir_instruction_graph.spl` imports at its
lines 3-5: Span, HirType, LayoutPhase, HirContractBlock. Its profile line reads
`qtype=4725/3781 miss`.

**The revert is not an endorsement of the drop.** Dropping the argument is the
original silent defect (d) measured (`Dict<text,MirType>` recorded as
`Dict<any,any>`, no diagnostic). Re-land both lanes only after the owner-scope
lookup follows the re-export hop to the declaring module, and only behind a
measured stage-1 census.

Full measurement, the failing-name census, and the honest limits (no unit
fixture reproduces it; per-commit attribution is static, not differential) are
in `hir_generic_projection_regression_run15_2026-08-22.md`.

## Follow-up (g) — generic-callable lane RE-LANDED ALONE for isolated measurement (2026-08-22)

`ec13c319250` reverted **two** lanes together — the generic-ARGUMENT projection
(`d481f15e1ac`) and this one, the generic-CALLABLE signature projection
(`86787968989`). That was a static attribution, not a differential one: at the
time there was no oracle short of a full stage-1 build, so both suspects went
out together. This section records that this lane was **reverted on suspicion,
not on evidence**, and is being re-landed ALONE so a run17 can measure it in
isolation.

### Counter-evidence that this lane is not the run15 cause

Blast radius of `86787968989` is exactly "callables with `type_params > 0`"
(plus a `Function` arm reachable only from projection). Occurrences of each NEW
run15 type name, by the construct that could carry it:

| run15 new name | in a GENERIC callable signature | as a generic ARGUMENT | as `T?` |
|---|---|---|---|
| HirContractBlock (472) | **0** | 0 | 6 |
| SymbolId (339) | **0** | 94 | 61 |
| ModuleSurfaceExportOrigin (145) | **0** | 2 | 0 |
| MirFunction (134) | 2 | 27 | 12 |
| HirType (124) | 1 | 53 | 100 |
| Span (111) | **0** | 0 | 58 |

The largest new population (HirContractBlock) has **zero** exposure to this
lane, as do Span and ModuleSurfaceExportOrigin. HirContractBlock's only
cross-module signature use is NON-generic —
`70.backend/backend/lean_backend.spl:528`,
`fn function_contract_from_hir(name: text, contract: HirContractBlock?, param_aliases: [(text, text)]) -> Result<FunctionContract, CompileError>`
— Optional + array-of-tuple + `Result` with generic ARGS, no type params at all.

Corroborating: a full `test/01_unit/compiler/hir` sweep run in both trees (the
landed tree, and the same commit with only `86787968989` reverted) produced
**byte-identical FAIL sets**, 48/48, 0 newly red and 0 newly green; the only
difference was this lane's own spec, which passes. A synthetic A/B on the exact
`function_contract_from_hir` shape plus bare `T?`, `Result<A, B>` and
`Dict<text, T>` measured 0 errors on both sides, so the shape does not
reproduce in isolation and real-module context is required.

**Stated limit, not papered over:** none of this reproduces the regression, so
it is "no exposure and no spec-level effect", NOT an exoneration. Run17 is the
oracle. If fatals explode again with this lane alone on the tree, it is this
lane's and it reverts with evidence.

**And the sweep evidence above is WEAKER than it looks** — recorded here rather
than left to flatter this lane. The bisect lane's point stands: the unit specs
cannot see this population at all (48 of 124 hir specs are red on BOTH sides,
and that lane's purpose-built facade-hop fixture is green on both), so a
byte-identical FAIL set is near-uninformative for the run15 question. It rules
out a spec-level regression and nothing more. The construct census and the
lean_backend shape are the load-bearing parts of the argument; the sweep is not.

The bisect lane reached the same conclusion independently and by a different
route (recorded on main at `a50b92999d2`): the victim
`50.mir/hwir/bit_vector_constant.spl` carries no `use` line at all yet reports
exactly the four `X?` optional fields that `mir_instruction_graph.spl` imports
at lines 3-5; the recursed ARGUMENT is looked up in the module the importer
NAMED — a facade/glob re-exporter — misses (`qtype=4725/3781 miss`), and falls
to `lower_type` in the importer's scope. That is the generic-argument/Optional
surface, not this one. Note also that `Option`/`Result`/`Dict` are NOT among
the 3716 fatals; their ARGUMENTS are.

Why this lane was reverted anyway, which is explicitly not a verdict against
it: (1) ENTANGLEMENT — `bound_type_params` and the `Function` arm share
parameter lists and recursion sites with the sibling's argument projection, so
reverting `d481f15e1ac` alone does not apply cleanly while this lane is
present; (2) the unit specs cannot discriminate, per the paragraph above;
(3) the only discriminating oracle is a stage-1 census. Re-land condition,
agreed by both lanes and the coordinator: a measured stage-1 `[hir-fatal]`
census at or below 48 fatals / 9 poisoned.

### What this re-land contains

Only `86787968989` + its two doc commits, cherry-picked onto the post-revert
tree. Verified to NOT drag in `d481f15e1ac`: the generic-ARGUMENT method
`imported_surface_projected_named_args` and both of its call sites appear **0
times** in the re-landed `module_callable_types.spl` (they arrived as
cherry-pick conflicts, from this lane's earlier rebase onto that sibling, and
were resolved OUT). The parity gate and spec that `ec13c319250` removed with
the sibling lane are likewise NOT restored here — they belong to that lane.

### run16 — the revert is confirmed to restore the tree, and this lane is cleared to re-land

`run16` (tree `ec13c319250`, BOTH generic lanes reverted) is terminal: `rc=1` at
4326s, **15 HIR fatals / 21 poisoned**, honest basis 16 distinct error lines.
That is at or below the post19 band the re-land condition named, `MirType` is
gone (was 180), and there is **no new error class**: run15's generic-name flood
(`Option` 1547, `Result` 962, `Dict` 889) is fully undone. So the revert did
restore the tree, and the re-land condition agreed by both lanes is met.

**Counting-basis caveat, recorded before anyone quotes the numbers.** run16's
**21 poisoned** vs post19's **9** may be a difference in COUNTING BASIS rather
than a real delta. post19's figure must be re-derived on run16's basis before
that gap is treated as a regression — comparing two censuses that were not
computed the same way is exactly the error that produced the false MirType
clearance prediction in follow-up (b) of this record.

What run16 does NOT establish: which of the two reverted lanes caused run15.
It removed both at once. This lane re-lands ALONE so `run17` can measure it in
isolation; `run17`, not run16, is what decides whether this fix stays.

## Follow-up (h) 2026-08-22 — FOURTH mechanism: the named provider module simply does not provide the type

Lane scope: the run16 census names `HirModule 2`, `VhdlPortDirection 2`,
`HirFunction 1`, `CompiledModule 1` (`error_census16.md`, tree `ec13c319250`,
15 distinct HIR fatals / 21 poisoned). AsmLocation/AsmConstraintKind belong to a
sibling lane and are untouched here.

### Mechanism (3 of the 4 names)

Three of them are **not** a projection defect at all. They are the TYPE-position
sibling of the already-fixed `unresolved name` import-reachability class
(`hir_unresolved_name_import_reachability_2026-08-22.md`): the caller writes

    use <provider>.{TypeName}

against a `<provider>` that neither DECLARES `TypeName` nor re-exports it, so
there is nothing to project, the annotation falls to `lower_type` in the
importer's scope, and HIR hard-errors. The seed resolves this leniently, which
is why the edges accumulated invisibly.

The compiler already prints the evidence itself, unprompted:
`[use-warning] '<Name>' is named in \`use <provider>.{...}\` but module '<file>'
does not provide it (imported from <caller>)`. That warning — not a new probe —
is the cheap oracle for this class, and a full stage-1 build is not needed to
find or verify a member of it.

| caller | type | named provider (pre-fix) | actually DECLARED in |
|---|---|---|---|
| `70.backend/backend/vhdl_type_mapper.spl` | `VhdlPortDirection` | *no import at all*; relied on `compiler.mir.mir_data.*` | `50.mir/mir_instruction_support.spl:104` |
| `70.backend/backend/vhdl/vhdl_design_catalog.spl` | `HirFunction` | `compiler.hir.hir_types` | `20.hir/hir_definitions.spl:35` |
| `80.driver/driver_pipeline_execution.spl` | `CompiledModule` | `compiler.backend.codegen` | `70.backend/backend/backend_types.spl:333` |

Controlled comparison, measured not inferred: `hir_types.spl` exports
`HirModule` (line 690) but nowhere declares or exports `HirFunction`;
`70.backend/codegen.spl` declares `CodegenPipeline` (line 673) but no
`CompiledModule` at all — the same `use` line carries one symbol that resolves
and one that cannot.

The `HirFunction` case is NOT the cycle the lane brief anticipated. The
declaration does not have to move: `hir_definitions.spl` does
`use compiler.hir.hir_types.*` for its own benefit, but `vhdl_design_catalog.spl`
is a BACKEND module, so importing `compiler.hir.hir_definitions.{HirFunction}`
there adds no edge into `20.hir` that does not already exist.

### Fix

Import each type from its DECLARING module. No resolver change, no diagnostic
suppressed, and — unlike the run15 lane — no facade hop is introduced, so the
50x flood shape is impossible by construction here.

### Evidence (runtime, isolated, minutes not 72 min)

`native-build` of the single failing file under
`SIMPLE_HIR_UNRESOLVED_TYPE_TRACE=1`, pristine `340d54e97bb` vs fixed tree:

| file | pre-fix `[hir-fatal]` | post-fix |
|---|---|---|
| `vhdl_type_mapper.spl` | `unresolved type: VhdlPortDirection` (x2) | **0** |
| `vhdl/vhdl_design_catalog.spl` | `unresolved type: HirFunction` | **0** |

`driver_pipeline_execution.spl` does not reach the fatal in an isolated
single-file closure (0 both sides) — stated rather than papered over; its
provider gap is proven statically by the table above and by `codegen.spl`
having no `CompiledModule` declaration or export.

### `HirModule` — NOT cleared, and it is a different shape

Recorded rather than guessed at. `src/compiler/mono/instantiation.spl`, the file
the run16 fatal names (`source_idx=683`, `errors=0->2`), **does not contain the
string `HirModule` anywhere**, and neither does anything it imports
(`00.common/compilation_context.spl` — no `use` lines at all, no `HirModule`) nor
its package `__init__`. A tree-wide sweep of every `use`/`export use` line naming
`HirModule` returns 13 sites and **all 13** import it from `compiler.hir.hir_types`,
which does declare (line 21) and export (line 690) it. So `HirModule` is NOT an
instance of the mechanism above, and there is no provider gap to repair.

Two facts constrain the next step: an isolated `native-build` of
`instantiation.spl` does not reproduce it (the errors it does produce are MIR
`unresolved method call`, not HIR), so the fatal needs a wider closure; and
run16 was recorded without `SIMPLE_HIR_UNRESOLVED_TYPE_TRACE`, so no
`[ist-proj-miss]`/`[field-dep-unresolved]` line exists for it anywhere. The
open hypothesis, untested: the reported NAME is wrong rather than the
resolution — `HirModule` is the FIRST declaration in `hir_types.spl`, i.e. the
index-0 entry of that module's type table, which is what a default/stale symbol
index would print. Next experiment: re-run a stage-1 build (or the smallest
closure that reaches `source_idx=683`) WITH the trace on, and read the
`lowering=src/compiler/mono/instantiation.spl` lines.
## Follow-up (i) — AsmConstraintKind / AsmLocation: a `use` line inside a docstring

Scope: the 12 of run16's 15 `[hir-fatal]` occurrences (8 of 14 file x type
pairs) carrying these two names. Sibling lane `49d764f48ae` took
VhdlPortDirection / HirFunction / CompiledModule; those are not claimed here.

**Not** the `use-warning` provider-does-not-provide mechanism that lane found,
and **not** the `type_params > 0` bail rejected in follow-up (d). Both were
tested and both are negative:

- `/usr/bin/grep -a use-warning stage1_build16.log | grep -E 'AsmLocation|AsmConstraintKind'`
  returns **zero lines**. There was never a provider complaint.
- `10.frontend/parser_types_expr.spl:803,809` really does declare
  `enum AsmConstraintKind` and `enum AsmLocation`, so the module the import
  named was correct all along.

**Mechanism: the two imports were never `use` STATEMENTS.**
`70.backend/backend/_CBackendTranslate/class_core.spl` carried
`use compiler.frontend.parser_types_expr.{AsmConstraintKind}` and `{AsmLocation}`
at lines **371-372**, in the middle of a triple-quoted docstring body attached to
the `bulk_copy` arm of `translate_intrinsic`. They are string CONTENT. The module
surface bound neither name, so `asm_constraint_for_c(kind: AsmConstraintKind,
location: AsmLocation)` had two unbindable signature dependencies. This also
explains the missing use-warning: a statement that does not exist cannot warn
about its provider, which is why the sibling lane's oracle is silent here and
why this needed its own lane.

The only `[hir-callable-dep-origin-unresolved]` line in run16 naming either type
named exactly this owner
(`owner=compiler.backend.backend._CBackendTranslate.class_core`). The four
modules that HARD-ERRORED — `70.backend/backend/c_backend_translate.spl`,
`c_codegen_adapter.spl`, `_CBackendTranslate/export_wrappers.spl`,
`instruction_lowering.spl` — import `MirToC` and (except the last) never name
either type: the "blamed on an innocent third party" behaviour this record
opened with, one owner accounting for all 8 pairs.

Second, smaller gap in the same family:
`_CBackendTranslate/instruction_lowering.spl` names `AsmConstraintKind` in four
match arms with no import at all (plain class A). Both fixed by putting a real
`use` line in the header; no resolver change, so the run15 generic-projection
flood shape is impossible by construction.

**Durable lesson this adds:** a whole-file grep for an import is not evidence the
import exists. `class_core.spl` would have passed any such check for months.
Import checks must be header-scoped.

Reproduce spec: `test/01_unit/compiler/hir/asm_owner_import_inside_docstring_spec.spl`
— 2 examples, **2/2 FAIL pre-fix, 2/2 PASS post-fix** on the deployed seed, with
a `names_type` guard-the-guard per example so the pin cannot pass vacuously if
`asm_constraint_for_c` or the match arms are refactored away, and a
header-scoped import predicate for the reason above.

Not claimed: this is a SOURCE fix. The facade-hop owner-scope resolution defect
from follow-up (e) is untouched and still open.

## Follow-up (i) 2026-08-23 — FIFTH mechanism: the OWNER reaches the type only through a glob (`HirModule`)

Follow-up (h) closed three of the four names in this lane's scope and left
`HirModule` open with an explicit "open hypothesis, untested" (a misreported
name via an index-0 symbol table). **That hypothesis is now refuted by
measurement, and the real mechanism is a fifth one.**

### The decisive evidence is the span, and it is EMPTY

There is exactly ONE fatal emit site in the tree —
`20.hir/hir_lowering/types.spl:957`, `self.error("unresolved type: {name}", span)` —
and it already carries a landed, level-gated probe whose comment states the
attribution caveat outright: *"the hard `unresolved type: X` is attributed to
the module being lowered, which is NOT necessarily the file the annotation came
from; the span carries the real file."*

Reproduced in **~40 minutes**, not a 72-minute full build, with a targeted
closure — `native-build --source src/compiler --entry-closure --entry
src/compiler/40.mono/__init__.spl` under `SIMPLE_HIR_UNRESOLVED_TYPE_TRACE=1`:

    [hir-unresolved-type-origin] name=HirModule
        lowering_module=src/compiler/mono/instantiation.spl span_file= span_line=0 span_col=0
    [hir-unresolved-type-origin] name=HirModule
        lowering_module=src/compiler/40.mono/__init__.spl   span_file= span_line=0 span_col=0

`span_file` is **empty** and `span_line=0`. The type node was never parsed from
any source file — it was **rebuilt by the imported-surface projection**. That is
the complete explanation for a name that appears nowhere in `instantiation.spl`,
nowhere in anything it imports, and nowhere in its package `__init__`.

Refuting the (h) hypothesis directly: `name` at that site is the same string the
failed symbol lookup used, so `HirModule` genuinely IS the name being resolved.
It is not an index-0 table entry printed in place of some other name, and the
`5c38b388a53` id-0 family does not apply.

### Root cause

The owner is `40.mono/monomorphize_integration.spl`. Its re-exported symbols

    fn run_monomorphization(modules: Dict<text, HirModule>) -> (Dict<text, HirModule>, MonoStats)
    class MonomorphizationPass   # me process_modules(modules: Dict<text, HirModule>) -> ...

name `HirModule` in their signatures, while the module reaches that name **only
through `use compiler.hir.hir_types.*`**. A glob is not a declaration, not a
re-export hop, and not an explicit import — the exact three-way test the
projection walk applies — so the projected surface carries no ORIGIN for
`HirModule`. The importer (`40.mono/__init__.spl`, which re-exports both symbols
at line 5/8, and `mono/instantiation.spl` through that package) then resolves the
name in ITS OWN scope, where it was never imported, and hard-errors.

This is the owner-missing-import class of this record's first section reached
from a new direction: previous instances had a *wrong* explicit import; this one
has *no* import statement at all, only a glob.

### Why both oracles were silent — and the durable lesson

`[use-warning]` (the cheap oracle follow-up (h) contributed) is silent **by
construction** here: it reports a brace-list import that names a symbol its
provider lacks, and there is no import statement at all to report.
`[hir-callable-dep-origin-unresolved]` is also silent — 0 lines for `HirModule`
across the reproducing build — the same silence follow-up (b) recorded for
`MirType`, and for the same reason (the projection walk never consults the
materialization walk).

The sibling Asm lane (`3858062cab6`) hit the identical silence from a third
surface form: its owner's two `use` lines sat **inside a triple-quoted
docstring**, i.e. string content, never statements. Shared durable lesson, now
enforced by this lane's spec:

> **A whole-file grep for an import is NOT evidence that the import exists.**
> The predicate must be HEADER-SCOPED — module level, outside docstrings and
> comments.

This lane's own earlier sweep made exactly that error (`^ *use .*HirModule`
matched 13 files and was read as "all 13 import it correctly"), which is why the
first pass concluded there was no provider gap. A tree-wide header-scoped sweep
finds **28** owners naming `HirModule` or `CompiledModule` in a type position
with no real import — a population, not a one-off. (A first version of that
sweep also mis-flagged `70.backend/backend/backend_helpers.spl`, whose
`CompiledModule` import is real but spans multiple lines: a predicate that does
not join brace-list continuations produces false positives in the other
direction. Both directions are recorded so the next lane inherits a correct
predicate.)

### Fix attempted — and the NEGATIVE RESULT, recorded not buried

Giving the owner the explicit import alongside its glob
(`use compiler.hir.hir_types.{HirModule}` in
`40.mono/monomorphize_integration.spl`) **did NOT clear the fatal.** Re-running
the same reproducing closure post-fix under the same trace:

    HIR lowering error in src/compiler/mono/instantiation.spl: unresolved type: HirModule
    HIR lowering error in src/compiler/40.mono/__init__.spl:  unresolved type: HirModule
    [hir-unresolved-type-origin] name=HirModule lowering_module=... span_file= span_line=0 span_col=0

Both fatals and both synthesized-span probe lines survive unchanged. So the
glob-only origin gap in `monomorphize_integration.spl` is **real and worth
fixing on its own terms** — the predicate below proves it, and it is a genuine
latent instance of this class — but it is **not** what produces these two
`HirModule` fatals. `HirModule` therefore stays OPEN, with the span evidence
above as the durable finding and the owner NOT yet identified.

What the negative result does establish, and what the next lane should start
from: the failing node is projection-built (empty span) and the name is
genuinely `HirModule` (single emit site, same string as the failed lookup), so
the remaining question is purely *which* surface projection builds it. The
existing `[ist-proj-miss]` / `[hir-callable-dep-origin-unresolved]` probes are
both silent for this name across the reproducing build, so the next step is a
probe at the projection site that prints the OWNER being projected, not another
static sweep. A candidate not yet excluded is the trait-typed field
`TemplateInstantiator.context: CompilationContext`, whose only implementing
class is `80.driver/pipeline/compiler_context.spl:16
class CompilerCompilationContext(CompilationContext)`.

### The population fix (landed regardless of the above)

The header-scoped sweep found **29** owners naming `HirModule` or
`CompiledModule` in signature position with no real import — reaching the name
only through a glob. These are latent fatals: they surface the moment their
importers lower far enough, the same "counts rise as more modules lower" effect
follow-up (b) measured when `HirModule` went 6 -> 8 while total fatals fell 81%.
All 29 now carry an explicit import from the DECLARING module. Verified not to
change behaviour: `simple compile` output is **byte-identical pre/post** on a
sample of the edited files (all pre-existing `runtime_file_rename` /
`char_code` / standalone-SMF limits, unchanged).

### `CompiledModule` — REOPENED, not closed by follow-up (h)

The Asm lane's run18 probe reports that importing `CompiledModule` from
`backend_types` did **not** clear `driver_pipeline_execution`. Follow-up (h)
already recorded that this name never reproduced in an isolated single-file
closure (0 fatals both sides) and that its gap was argued statically — that
caveat is now load-bearing, and the name is treated as OPEN. The static defect
(h) repaired is real and independently verifiable — `70.backend/codegen.spl`
declares `CodegenPipeline` at line 673 and no `CompiledModule` anywhere, so the
old import named a symbol its provider does not have — but it is evidently not
the whole cause. Next evidence: the `name=CompiledModule` line from the traced
run19 full build, read the same way as above.

### Ratchet

`scripts/check/check-signature-type-import-provenance.shs` — fail-closed, house
style, verdict as the last line of stdout, `--selftest` fatal and
non-optional. Measured: `PASS — 1809 file(s) checked, 0 offender(s)` on the
fixed tree in **5 seconds**, and `FAIL — 1809 file(s) checked, 29 offender(s)`
on the pristine tree, so it is proven to discriminate rather than merely be
green. Types are data (`signature_type_import_provenance_types.txt`, `<Type>
<declaring-module>` rows), so extending it to a newly-found type is a one-line
change.

The 8 selftest fixtures encode both directions of the header-scoping lesson,
because both directions have already cost a lane real time:
must-FAIL — glob-only (the incident shape), an import-shaped line **inside a
docstring** (the Asm lane's shape), and a **commented-out** import;
must-PASS — a real single-line import, a real **multi-line brace-list**
continuation (the false positive this lane's own first sweep produced), and a
type named only in a comment;
non-vacuity — an empty tree must scan 0 files and an empty types table must
have 0 rows, each forcing ERROR rather than a pass.

Scope note: like the C-runtime guard and unlike the range-based guards, this
checks a TREE, not a `BASE..NEW` delta — import provenance is a property of a
tree, and a push that edits only the DECLARING module can strand an importer it
never touched. It also de-duplicates by realpath, because `src/compiler/mono` is
a SYMLINK to `40.mono` and a naive walk double-counts every mirrored file.
