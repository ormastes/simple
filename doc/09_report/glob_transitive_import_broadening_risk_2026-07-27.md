# Glob transitive-import broadening — risk assessment

Date: 2026-07-27
Scope: `67024e9c0a51` change **(b)** — one-level transitive star-import sweeping in
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`.
Analysis is READ-ONLY. No source was modified.

**Recommendation up front: REVERT (b). Do not keep it, and do not keep the guard.**
It is already effectively gone at HEAD (in a broken state), its motivating symbol is
now covered by change (a), and the residual gap is 13 names that are cheaper to fix
with one edit to an `export` line than with a compiler semantics change.

---

## 0. HEADLINE: (b) is not actually live at HEAD — it is broken code

This is the single most important finding and it reframes the whole question.

| Commit | `glob_star_*` (the (b) impl) | `register_glob_imported_symbols_depth` call | `declaration_count` guard |
|---|---|---|---|
| `834006c5afa` (pre) | 40 | 0 | 0 |
| `67024e9c0a51` (the change under review) | **40** | 0 | 0 |
| `69b1b2ab5dc` "sync gh and push" | **0** | **1** | **2** |
| `559832a135b`, `70a75df5a18`, `b0698c98307`, HEAD `e9d7966e7bb` | 0 | 1 | 2 |

At HEAD, `register_glob_imported_symbols` spans
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:693`–`779`
(verified: the next `me` definition is `resolve_import_symbols` at :781). Inside it:

- `module_lowering.spl:761` — `if depth == 0 and declaration_count == 0 and glob_imp.items.len() == 0:`
- `module_lowering.spl:765` — `self.register_glob_imported_symbols_depth(nested_mod, nested_key, import_span, depth + 1)`

Both references are **unresolvable**:

- `depth` is **not** a parameter of `register_glob_imported_symbols` (signature at :693 is
  `(imported_mod: any, imported_mod_name: text, import_span: Span)` — no `depth`).
  It is not a field of `HirLowering` either (`src/compiler/20.hir/hir_lowering/types.spl:44`
  declares `loop_depth: i64` at :52, no `depth`), and there is no module-level `depth`.
- `register_glob_imported_symbols_depth` is **defined nowhere in the repo** — a
  repo-wide grep of `src/` returns exactly one hit, the call site at :765 itself.
  (Whether it ever existed anywhere in history is **unverified**: the `git log -S --all`
  probe timed out at 2 minutes. It is absent from every commit sampled above.)

So the inline 40-line transitive sweep that `67024e9c0a51` added was **replaced** by the
sync commit `69b1b2ab5dc` with a guarded call to a helper that does not exist. The
line `761` condition is inside the `while glob_imp_idx < imported_mod.imports.len()` loop
at :758 and is therefore reached on **every glob import**, so this is not dead code that
merely fails to fire — it is a live unresolved-name/unresolved-method site on the hot path.

Two consequences:

1. Any measurement of "(b) reduces errors 4,008 → 2,224" describes `67024e9c0a51`'s tree,
   **not** HEAD. Re-measuring at HEAD is required before any claim about (b)'s value.
2. This is exactly the failure mode `.claude/rules/vcs.md` § "Sync must never clobber"
   warns about: a `sync gh and push` commit whose parent is `834006c5afa` (**not**
   `67024e9c0a51`) landed a stale/parallel version of this file over the reviewed work.

`67024e9c0a51`'s own commit message flagged (b) as needing a semantics decision. The
tree has since drifted into a third state that is neither "(b) kept" nor "(b) reverted".
That must be resolved regardless of which option is chosen.

---

## 1. Mechanism — what (b) registers, and under what name

### 1a. The registration primitive

`register_imported_symbol` (`module_lowering.spl:~470`–`541`) dispatches on which decl
dict of the source module contains `imported_name`, in this order:

| Source dict | Registered as | Line |
|---|---|---|
| `classes` | `SymbolKind.Class`, then `rename_symbol(sym, imported_name)` + method registration | :482–485 |
| `structs` | `SymbolKind.Struct` + rename + methods | :486–489 |
| `enums` | `SymbolKind.Enum` + rename + methods | :490–493 |
| `traits` | `SymbolKind.Trait`, plus on-demand `lower_trait` into `self.lowered_traits` | :494–519 |
| `type_aliases` | `SymbolKind.TypeAlias` | :520–521 |
| `functions` | `SymbolKind.Function` with `declared_callable_type`, then `qualify_imported_function_symbol` | :522–525 |
| `constants` | `SymbolKind.Const` | :526–527 |
| none of the above | falls through to `find_reexport_source` (`:536`), re-entering `register_imported_symbol` on the *defining* module (`:541`) | :528–541 |

Every `define` call passes `Some(imported_mod_name)` as the owning module and
`Visibility.Public`.

**Naming.** For types, the symbol is defined under `local_name` and then
`rename_symbol`d to `imported_name` (:484, :488, :492) — under a glob sweep those are
identical, so the symbol carries its bare declared name.

For **functions**, `qualify_imported_function_symbol` (`module_lowering.spl:671`–`691`)
renames the stored symbol to `"{imported_mod_name}.{imported_name}"` — but **only** when
both `SIMPLE_BOOTSTRAP=1` and `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1` (:688–691). This
matters for (b): the module name baked into the symbol is the one passed to
`register_imported_symbol`. In `67024e9c0a51`'s implementation the transitive sweep passed
`glob_star_key` — the *level-2* module's canonical key, not the facade's — so under an
entry-closure bootstrap build a transitively swept function is qualified as
`compiler.mir.mir_instructions.mir_operand_copy`, i.e. it names the true definer. That is
correct and is the one unambiguously good property of (b)'s implementation.

### 1b. What (b) sweeps

Per `67024e9c0a51`'s diff, for each import of the glob-imported facade `A` with
`items.len() == 0` (i.e. `A` itself does `use B.*`), resolve `B` via `resolve_module_key`
and sweep **six** dicts of `B` — `functions`, `classes`, `structs`, `enums`, `traits`,
`constants` — registering each key through `register_imported_symbol(B, B_key, k, k, span)`.

Note the asymmetry with the direct sweep at `:694`–`734`, which covers **seven** dicts
including `type_aliases` (`:718`–`722`). (b) omits `type_aliases`. One level deep,
explicitly not recursive.

### 1c. Two pre-existing defects in the same function (incidental, low severity)

- **Duplicated export sweep.** `module_lowering.spl:739`–`748` (while-loop) and
  `:776`–`779` (for-loop) perform the identical `exports` walk, both skipping
  `.*`-suffixed items and both calling `register_imported_symbol(..., item, item, ...)`.
  Idempotent, so harmless, but one is dead.
- **Enum lowering path does not see (b).** `lower_module`'s glob branch at
  `module_lowering.spl:1359`–`1373` walks only `module.imports` (direct star imports) to
  populate `lower_module_enums`. A transitively swept enum gets a *symbol* from (b) but no
  entry in the enum-lowering table — a latent inconsistency between symbol visibility and
  enum lowering. **Unverified** whether this is observable; no repro was attempted.

---

## 2. Shadowing risk

### 2a. Is the mechanism theoretically live? Yes.

`resolve_import_symbols` (:781) is called before local declarations are registered, and
`module_lowering.spl:1368`–`1370` states the rule explicitly:

> `# Imports are registered before local declarations and`
> `# type symbols are first-write-wins, so the imported`
> `# definition must win here too.`

So a transitively swept name that collides with a local declaration in the importing
module **would** win, and the collision is silent — `register_imported_symbol` has no
duplicate detection and emits no diagnostic. A call would then resolve to the
transitively-imported definition instead of the module's own.

### 2b. Measured: the risk is real but narrow

A scan of all 1,497 `.spl` files under `src/`, modelling the sweep for the 12
most-star-imported facades, found **exactly one** actual collision:

| Colliding name | Importing module M's own decl | Competing level-2 decl | Facade A that links them |
|---|---|---|---|
| `OptimizationLevel` (enum) | `/home/ormastes/dev/pub/simple/src/compiler/70.backend/backend/optimization_passes.spl:12` | `/home/ormastes/dev/pub/simple/src/compiler/70.backend/backend/backend_types.spl:228` | `compiler.backend.backend_types` |

Per-facade sweep sizes (level-2 names swept / importer count / collisions):

| Facade | Own decls | Level-2 star targets | L2 names | Importers | Collisions |
|---|---|---|---|---|---|
| `compiler.mir.mir_data` (`src/compiler/50.mir/mir_data.spl`) | 10 | `mir_types`, `mir_instructions` | 54 | 99 | 0 |
| `compiler.hir.hir` (`src/compiler/20.hir/hir.spl`) | 0 | `hir_types`, `hir_definitions` | 66 | 35 | 0 |
| `compiler.mir.mir` (`src/compiler/50.mir/mir.spl`) | 0 | 4 modules | 29 | 28 | 0 |
| `compiler.hir.hir_types` (`src/compiler/20.hir/hir_types.spl`) | 22 | `parser_types`, `parser_types_expr` | 74 | 27 | 0 |
| `compiler.hir.hir_definitions` (`src/compiler/20.hir/hir_definitions.spl`) | 44 | `hir_types` | 22 | 24 | 0 |
| `compiler.backend.backend_api` (`src/compiler/70.backend/backend/backend_api.spl`) | 1 | `mir_data` | 10 | 21 | 0 |
| `compiler.frontend.parser_types` (`src/compiler/10.frontend/parser_types.spl`) | 33 | `parser_types_expr`, `parser_types_utils` | 46 | 20 | 0 |
| `compiler.backend.backend_types` (`src/compiler/70.backend/backend_types.spl`) | 16 | `hir.hir`, `mir.mir`, `backend.backend.backend_types` | 17 | 13 | **1** |
| `compiler.traits.traits` (`src/compiler/25.traits/traits.spl`) | 0 | 5 modules | 17 | 10 | 0 |
| `compiler.frontend.core.lexer` (`src/compiler/10.frontend/core/lexer.spl`) | 84 | none | — | 27 | 0 |
| `compiler.mdsoc.types` (`src/compiler/85.mdsoc/types.spl`) | 0 | none | — | 16 | 0 |
| `compiler.hir.inference.types` (`src/compiler/20.hir/inference/types.spl`) | 14 | none | — | 13 | 0 |

`src/compiler/{backend,hir,mir,frontend,traits,mdsoc,common}` are symlinks to the numbered
directories; results are deduped by realpath. The module-name → path mapping (numeric-prefix
stripping) was inferred from directory layout, **not** read from a resolver implementation —
**unverified**. Whether `export use X.*` participates in the sweep identically to plain
`use X.*` is also **unverified**; both were treated as star imports. If `export use` is
excluded, `compiler.hir.hir` sweeps nothing and its 35 importers are trivially safe.

### 2c. The latent hazard is larger than the current collision count

271 distinct capitalized type names are declared in more than one module under
`src/compiler`; 76 of them are ≤9 characters. Worst offenders by module count:

| Name | Modules | First competing sites (all under `/home/ormastes/dev/pub/simple/src/compiler/`) |
|---|---|---|
| `Symbol` | 35 | `00.common/effects.spl:24` (type) · `20.hir/hir_types.spl:90` · `25.traits/trait_method_resolution.spl:9` · `30.types/associated_types_defs.spl:12` |
| `HirType` | 27 | `20.hir/hir_types.spl:620` (**struct**) vs `25.traits/trait_method_resolution.spl:15` (**enum**) · `30.types/bidir_phase1a.spl:56` (**enum**) |
| `InferMode` | 7 | `30.types/bidir_phase1a.spl:15`, `1b:12`, `1c:13`, `1d:16` · `bidirectional_types.spl:19` · `type_infer_types.spl:223` · `type_system/bidirectional.spl:26` |
| `MacroDef` | 6 | `10.frontend/parser/macro_registry.spl:109` (**struct**) vs `30.types/macro_def.spl:123` (**class**) · `macro_checker_phase7a:116`, `7b:83`, `7c:85` · `35.semantics/macro_check/mod.spl:47` |
| `TraitRef` | 6 | `25.traits/trait_method_resolution.spl:60` · `30.types/associated_types_defs.spl:73`, `phase4a:51`, `4b:60`, `4c:63`, `4d:66` |
| `Expr` | 5 | `10.frontend/parser_types_expr.spl:172` (**struct**) vs `30.types/macro_def.spl:57` (**enum**) · `macro_checker_phase7a:52`, `7b:49`, `7c:49` |
| `MacroRegistry` | 5 | `10.frontend/parser/macro_registry.spl:128` · `30.types/macro_def.spl:184` · `phase7a:177`, `7b:119`, `7c:108` |
| `HirExpr` | 5 | `20.hir/hir_definitions.spl:422` · `30.types/bidir_phase1a:108`, `1b:57`, `1c:91`, `1d:87` |
| `HirExprKind` | 5 | `20.hir/hir_definitions.spl:431` · `bidir_phase1a:98`, `1b:48`, `1c:81`, `1d:74` |
| `TypeInferencer` | 5 | `30.types/bidir_phase1a:138`, `1b:88`, `1c:111`, `1d:119` · `bidirectional_inferencer.spl:19` |
| `Kind` | 5 | `30.types/higher_rank_poly_types.spl:14`, `phase5a:15`, `5b:15`, `5c:15`, `5d:15` |
| `TypeVar` | 5 | `30.types/higher_rank_poly_types.spl:47`, `phase5a:48`, `5b:30`, `5c:30`, `5d:30` |

Counts for the names named in the task brief: `Symbol`=35, `Token`=4, `Type`=3, `Span`=2,
`Result`=2, `Scope`=2, `Value`=1, `Config`=1, `Module`=1, `Context`=0, `Error`=0.

The `30.types/*_phase*` clusters are **local shim copies** that redeclare `HirType`,
`Symbol`, `HirExpr`, `Expr` rather than importing them. They do not currently star-import
the corresponding facade, so they are latent, not active. **They become live collisions the
moment any one of them switches to `use compiler.hir.hir.*`** — and several would then be
struct-vs-enum kind mismatches (`HirType`, `MacroDef`, `Expr`), which is the worst class:
first-write-wins would hand a `struct` symbol to code written against an `enum`.

**Assessment:** (b)'s blast radius today is 1 collision. Its blast radius under any future
refactor toward barrel imports is materially larger, and the failure is silent by
construction.

### 2d. The `declaration_count == 0` guard does not protect the motivating case

The guard attempted at `module_lowering.spl:760`–`761` fires only when the facade declares
nothing at all. Applied to the table in §2b:

- `mir_data` declares **10** items (`struct MirBuilder` at `src/compiler/50.mir/mir_data.spl:28`,
  plus `bootstrap_fn_*` functions at :651–:730) → **guard excludes it**. But `mir_data` is
  the entire motivation for (b): `mir_operand_copy`, 393 errors, 98–99 star importers.
- `backend_types` declares 16 → **guard excludes it**. That is the one module carrying the
  one real collision (`OptimizationLevel`).

So the guard variant is the worst of both worlds: it suppresses (b) exactly where (b) was
supposed to help, while the facades it *does* permit (`hir.hir`, `mir.mir`, `traits.traits`
— all 0-decl barrels) are precisely the ones already fully covered by change (a)'s
`export`-list sweep. **The guarded option is functionally equivalent to reverting (b),
with extra code.**

---

## 3. Cost of the stricter alternative — much lower than the commit message implies

### 3a. The headline symbol no longer needs (b)

`67024e9c0a51`'s message states mir_data "never re-exports `mir_operand_copy`". That was
true at the time. **It is false at HEAD.** `src/compiler/50.mir/mir_data.spl` now exports it
twice — `:624` (`export mir_operand_copy, mir_operand_move, mir_operand_const_int`) and
`:734` (`export mir_operand_copy, mir_operand_const_int`):

| Commit | `^export .*mir_operand_copy` lines | total `export` lines |
|---|---|---|
| `834006c5afa`, `67024e9c0a51` | 0 | 14 |
| `69b1b2ab5dc` | 1 | 19 |
| `70a75df5a18`, `b0698c98307`, HEAD | **2** | 20 |

Change **(a)** — the uncontroversial `export`-list sweep at `module_lowering.spl:739`–`748` —
already resolves `mir_operand_copy` and every other name on those 20 lines. **The 393-error
symbol that justified (b) is covered without (b).**

### 3b. Residual gap: 13 symbols, 28 files

Computing (level-2 declarations) − (facade exports ∪ facade own decls) for the risky facades:

| Facade | L2 decls | Covered by exports+own | Residual reachable **only** via (b) |
|---|---|---|---|
| `mir_data` | 54 | 43 exports + 10 own | **22** |
| `backend_types` | 17 | 17 + 17 | 14 |
| `hir_types` | 74 | 23 + 23 | 74 |

But raw residual counts overstate the work. Filtering the mir_data residual to names
actually referenced by one of its 98 star-importers, in a file with no explicit import:

| Uses | Symbol |
|---|---|
| 6 | `MirStatic` |
| 6 | `MirFieldDef` |
| 5 | `MirPlace` |
| 5 | `MirConstant` |
| 3 | `MirVariantDef` |
| 3 | `GpuMemoryScope` |
| 3 | `GpuBarrierScope` |
| 2 | `VhdlProcessKind` |
| 2 | `MirTypeDefKind` |
| 2 | `mir_signature_params` |
| 2 | `mir_fold_binop` |
| 1 | `VhdlPortDirection` |
| 1 | `vhdl_clock_domain_from_metadata` |

**13 distinct symbols, ~41 use sites, 28 of 98 files.** The other 9 residual names
(`LayoutPhase`, `MirProjection`, `mir_local_id`, `mir_signature`, `mir_signature_simple`, …)
are unused by star-importers and cost nothing.

### 3c. The cheapest fix is not "explicit imports" at all

The 13 names are all legitimately part of mir_data's public surface — they are MIR data
types, exactly what a `mir_data` facade exists to expose. Adding them to the facade's
`export` list is **one or two new `export` lines** in
`src/compiler/50.mir/mir_data.spl`, after which change (a) resolves all 41 use sites with
**zero** edits to the 28 consumer files. That is strictly smaller than (b)'s 40 lines of
compiler code, and it is declarative: the facade author states the surface, rather than the
resolver guessing it.

Even the pessimistic path — 28 files × one `use compiler.mir.mir_instructions.{…}` line —
is a small mechanical change, not a large one. Either way the "revert (b)" cost is
**hours, not days**, and far below the cost of the silent-shadowing class in §2c.

The same shape applies to `backend_types` (14 residual) and would need a separate pass for
`hir_types` (74 residual — the largest, and **unverified** how many are actually used by
its 27 importers; that measurement was not run).

---

## 4. Recommendation

### REVERT (b). Do not adopt the guard.

Ranked evidence:

1. **(b) is already gone at HEAD, in a broken state.** `module_lowering.spl:761,765` call an
   undefined `depth` and an undefined `register_glob_imported_symbols_depth`. Whatever is
   decided, this must be repaired. "Revert" is the smallest repair: delete `:757`–`772`'s
   nested-sweep branch (keeping the `glob_imp.items` loop at :766–:771), leaving the code
   in a state that compiles and matches its comments.
2. **(b)'s motivating symbol no longer needs it.** `mir_operand_copy` is exported at
   `src/compiler/50.mir/mir_data.spl:624` and `:734`, resolved by change (a). The 393-error
   justification has been overtaken by events.
3. **The guard cannot help.** `declaration_count == 0` excludes `mir_data` (10 decls) and
   `backend_types` (16 decls) — the only two facades where (b) mattered. It permits only
   0-decl barrels, which (a) already covers. It is dead weight.
4. **The residual cost is trivial and better solved declaratively.** 13 symbols / 28 files,
   fixable by extending one `export` list — a smaller diff than (b) itself.
5. **The risk is silent and grows.** 271 duplicated type names, several struct-vs-enum
   (`HirType` at `20.hir/hir_types.spl:620` vs `30.types/bidir_phase1a.spl:56`), with
   first-write-wins (`module_lowering.spl:1368`–`1370`) and no duplicate diagnostic. One
   active collision today (`OptimizationLevel`), but the `30.types/*_phase*` shim clusters
   arm a much larger set behind a single future refactor.

**Keep (a) unchanged.** An `export` list is an explicit author promise; sweeping it is
correct and carries none of this risk.

### Secondary recommendations

- Repair the `69b1b2ab5dc` sync clobber properly rather than patching around it, and note
  it as another instance of `.claude/rules/vcs.md` § "Sync must never clobber" (parent
  `834006c5afa` ≠ `67024e9c0a51`).
- Delete the duplicated export sweep — keep `module_lowering.spl:739`–`748`, drop
  `:776`–`779` (or vice versa).
- Consider adding `type_aliases` to the direct sweep's coverage audit; (b) omitted it,
  which suggests the seven-vs-six dict lists have drifted. **Unverified** whether this
  causes any current failure.
- **File a separate defect** for the silent-shadow class independent of this decision: a
  duplicate registration in `register_imported_symbol` should at minimum warn when the
  incoming `SymbolKind` differs from an existing symbol of the same name. That is the
  guard that actually addresses §2c, and it is orthogonal to (b).

### Validating test

The decision is validated by a **resolution-target** test, not an error-count test — the
error-count metric is what made (b) look good in the first place.

1. **Re-measure at HEAD first.** The 4,008 → 2,224 figure describes `67024e9c0a51`'s tree.
   Establish HEAD's number after repairing `:761`/`:765`, both with and without the nested
   branch. If the two numbers are equal, (b) contributes nothing and the decision is settled
   empirically.
2. **Resolution-target assertion (the real test).** Add an SSpec under `test/` that lowers a
   synthetic three-module fixture — `B` declares `struct Widget`; facade `A` does
   `use B.*` and declares its own items; `M` does `use A.*` **and** declares its own
   `struct Widget` — then asserts the symbol `Widget` in `M`'s scope resolves to **M's**
   definition (owner module == `M`), not `B`'s. Under (b) this fails; under revert it passes.
   This is the test that would have caught the shadowing class the commit message worried
   about, and it does not exist today.
3. **Regression guard for (a).** A fixture asserting `use A.*` resolves a name that `A`
   only re-exports (the `mir_operand_copy` shape), so a future revert of (b) cannot be
   mistaken for a revert of (a).
4. **Real-tree check.** After reverting, confirm the 13 symbols in §3b resolve — either via
   extended `export` lines or explicit imports — with no new unresolved names in the
   stage-4 full-CLI error set.

---

## Explicitly unverified

- Whether `register_glob_imported_symbols_depth` ever existed in repo history (`git log -S --all` timed out at 120s).
- Module-name → file-path mapping convention (numeric-prefix stripping); inferred from directory layout, not read from a resolver.
- Whether `export use X.*` participates in the sweep identically to plain `use X.*`.
- How many of `hir_types`' 74 residual level-2 names are actually used by its 27 star-importers.
- Whether the enum-lowering inconsistency in §1c (`module_lowering.spl:1359`–`1373` sees only direct imports) is observable in practice.
- No compiler was built or run; `lsp_diagnostics` is unavailable in source mode. All findings are from static reading and grep.
