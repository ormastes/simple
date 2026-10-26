# Design: target-neutral HIR for declaration-level @cfg and binding @when chains

Status: proposal (docs only). Plan: `doc/03_plan/compiler/hir_target_neutral_mir_target_plan.md`.
Placed under `frontend/` because `doc/05_design/compiler/` already holds 49 entries
(fanout limit 10); new files go in a subdirectory.

## 0. Where we are

| Landed | Effect |
|---|---|
| #4943 | `HirExprKind.CfgSelect(conds: [text], arms: [HirBlock], else_: HirBlock?)`, appended last so codec ordinals stay positional (`src/compiler/20.hir/hir_definitions.spl:681-684`). |
| #4954 | With `SIMPLE_HIR_CFG_SELECT=1`, indented body-level `@when` chains become `if __cfg_when__("cond")` chains (`10.frontend/core/parser_preprocessor.spl:383-388`), lowered to `CfgSelect` by `20.hir/hir_lowering/_Expressions/cfg_when_marker.spl`; the rewrite is at `parser_preprocessor.spl:491-504`. MIR picks the arm in `lower_cfg_select` (`50.mir/_MirLowering/asm_and_targets.spl:111-135`) via the pure `mir_cfg_select_arm` (`50.mir/mir_cfg_select.spl`, no env, no globals). |

Still stripped before HIR (the preprocessor deletes losing arms; `_pp_eval_condition`
reads the ambient target, `parser_preprocessor.spl:19-29,246`):
1. per-declaration `@cfg(...)` on fn/struct/class/impl/extern/use/val (module or impl level);
2. top-level (column-0) `@when/@elif/@else/@end` chains;
3. statement chains whose arms declare bindings (`_pp_chain_marker_ok` returns false when a
   line at the chain's indent starts `val/var/let`, `parser_preprocessor.spl:415-455`).

Consequence: the HIR cache key must still carry the target (`80.driver/driver_hir_cache.spl:163-170`,
tag `WA(hir-target-neutral)`), so one HIR cannot serve all targets.

## 1. Declaration-level representation

Constraints. `HirModule` (`20.hir/hir_types.spl:24-46`) is `Dict<SymbolId, X>` stores plus
`symbols: SymbolTable`, `imports`, `impls: [HirImpl]`. Items register by name during module
build (`20.hir/hir_lowering/_Items/module_build.spl`, `module_declarations_bootstrap.spl`,
`module_import_registration.spl`). Today a name defined in two arms never coexists, so the
table assumes one definition per name.

### Option A: wrapper node `HirCfgDecls{conds, arm_items, else_items}`
New `HirModule.cfg_decls: [HirCfgDecls]` (and `HirImpl.cfg_members`), arms holding bags of items.
- Pro: same shape as `CfgSelect`; a top-level chain maps 1:1; existing dicts stay "unconditional
  items only"; dropping an arm is one operation.
- Con: every consumer of `functions/structs/...` (typing, coherence, export computation,
  codegen driver, LSP) must also walk `cfg_decls`: two parallel item stores. A lone
  `@cfg(os="linux") fn foo` needs a synthetic one-arm wrapper with an empty else.

### Option B: per-item guard `cfg: [text]` on HirFunction/HirStruct/HirClass/HirEnum/HirTrait/HirConst/HirImpl/HirImport
Items stay in the existing dicts; an unguarded item has `cfg_group == 0`. Each item records its own
arm condition plus chain identity `(cfg_group, cfg_arm)`; exclusivity comes from the identity.
- Pro: no new store; all iteration sites keep working and merely gain a filter; a single
  `@cfg` is exactly the representation; impl members and imports reuse it.
- Con: first-match chain semantics is re-expressed as independent predicates; more text per
  item; same-name items now coexist in one dict (see symbol tables).

### Recommendation: Option B, with (cfg_group, arm_index) guards
Add `cfg: [text]`, `cfg_group: i64` (chain id, 0 = none) and `cfg_arm: i64` (index in the
chain, -1 = else) to each declaration struct. Declaration kinds covered include `me`,
`static`, `extern`, `@init` and `val/var/const` (`_pp_target_decl_kind`, `parser_preprocessor.spl:306-320`).
`cfg` holds the arm's own condition text only (not the negated priors), in the grammar
`mir_cfg_select_arm` already parses, so there is no second evaluator. MIR evaluates each
group once, first match wins, exactly like `lower_cfg_select`, and enables the items whose
`cfg_arm` equals the winner. Exclusivity of arms is therefore group identity plus arm index, not
a property recomputed from predicates. This also answers the earlier question on guard text bloat.

Effective guard. Every implication, disjointness and signature check uses an arm's EFFECTIVE
guard: its own condition AND NOT every lower-indexed sibling's condition in the same `cfg_group`
(the `else` arm: NOT all of them). It is derived from the group at check time; no negations are
stored. So a caller in an `os=windows` region implies the windows arm's effective guard and is
never typed against the `@else` variant, even though `@else` has no condition of its own.

Implication and disjointness (including across groups) are evaluated over the finite os x arch
matrix: enumerate every (os, arch) pair the evaluator knows, evaluate both effective guards per
pair, and require "use true implies def true" (or "never both true" for disjointness) for all
pairs. `feature` atoms are free boolean variables: each distinct atom is enumerated over both
truth values within the matrix. Unknown atoms are an error, as in MIR.

### Symbol tables and name resolution (same name in two arms)
- `SymbolId` stays unique per definition, not per name. The module symbol table maps
  `name -> [SymbolId]` for guarded names (entry holds ids and guards); unguarded names stay single.
- Registration rejects overlap: same `cfg_group` with different `cfg_arm` is legal; an unguarded
  definition plus any guarded sibling of the same name is a duplicate error; two definitions in
  different groups whose guards are both satisfiable on some os x arch pair are a duplicate error.
- Call-site binding. HIR binds each `Call`/`Path` to ONE canonical id of the group (the first
  arm in source order), not to a set. MIR remaps it: the callee's `cfg_group` is looked up and the
  reference is redirected to the sibling whose `cfg_arm` is enabled for the target. No new
  expression kind is needed; the per-module group index (`cfg_group -> [SymbolId]`, built at
  registration) is the only table, keyed by group id and never by guard text.
- Signature rule. A caller inside a region whose guard implies one variant's guard (matrix
  check above) type-checks against that variant's signature. An unguarded caller requires all
  variants to have identical parameter and return types; otherwise error `E-CFG-SIG-DIVERGE`
  naming both arms. So `fn foo` in windows and linux arms with different signatures is legal when
  its callers are themselves guarded, which is how platform code is written today.
- Standalone `@cfg` items (no chain, so no group yet): each gets its own fresh `cfg_group` with
  `cfg_arm` 0. Two same-named standalone items (`@cfg(os="windows") fn f`, `@cfg(os="linux") fn f`)
  may coexist only if their guards are proven disjoint over the finite os x arch matrix (feature
  atoms syntactic); the registrar then merges them into one canonical group and renumbers `cfg_arm` in source order. Otherwise: overlap
  error (same signature) or `E-CFG-SIG-DIVERGE`.
- The five name-keyed indexes in `SymbolTable` (`20.hir/hir_types.spl:300-313`) plus `Scope`
  (`:264`) each need a defined multi-variant behaviour. Rule for all: key stays the plain name, value
  becomes the canonical group id (the arm-0, first-in-source-order variant's `SymbolId`), and variants are listed by
  the group.
  - `exact_symbols`: name -> canonical id; variants reachable via the group.
  - `qualified_functions`, `qualified_types`: `mod.name` -> canonical id; a type group requires equal
    generic arity across arms, else error.
  - `module_callables`: canonical id; callable type is the common signature or, when divergent, marked
    "group-divergent" so unguarded callers are rejected (`E-CFG-SIG-DIVERGE`).
  - `root_scope_symbols`: canonical id; shadowing rules are unchanged because one name occupies one slot.
  - `Scope`: a guarded region pushes a guard context so lookups inside prefer the variant its guard implies.
  No index is keyed by guard text, so no `cfg_resolution` table exists.
- Imports: `HirImport` gets the same `cfg`. A guarded `use` registers its names as guarded
  symbols (`module_import_registration.spl`); an unguarded use of such a name is an error
  unless covered by the same guard. The driver import closure (`closure_digest`,
  `driver_hir_cache.spl:143`) stays target-neutral: HIR loads every guarded import regardless of
  target, and the skip happens in MIR (a false-guard import emits no link or codegen dependency).
- Trait impl lowering lives at `20.hir/hir_lowering/_Items/trait_impl_lowering.spl` (e.g.
  `record_impl_textual_method_keys`, `:216`) and runs at HIR-lowering time with no target.
  It stays target-free: it records every guarded impl with its `(cfg_group, cfg_arm)`; the
  overlap decision moves into the guard-aware pass in `30.types/type_system/checker.spl` below.
- Re-exports (`module_reexport_materialization.spl`) inherit the guard of the underlying decl.

### Type checking each variant
Each variant is type-checked once, target-neutrally, with its guard in scope, referencing only
its own arm plus unguarded names. That surfaces errors in non-selected arms. Layout-dependent
queries are the exception (section 5). To bound cost, v1 checks a variant lazily when the item
is reachable under a configured target set (`--cfg-check-targets`, default build target plus
host); later widen to all variants.

### How MIR / mono drops non-selected items
`50.mir/_MirLowering/module_lowering.spl` evaluates each item's guard with a new
`mir_cfg_item_enabled(group, arm, conds, ctx, features)` (picks the group winner once) beside `mir_cfg_select_arm` (malformed condition
is fatal, same as `lower_cfg_select` idx == -2). Items whose arm lost are skipped before
lowering, so they never reach monomorphization queues or codegen. Instantiation requests that
name a dropped variant are errors (the caller lacks the matching guard). An impl whose own guard
is false is dropped; per-member guards drop members.

Coherence must be guard-aware in `30.types/type_system/checker.spl` (coherence tracking at L55,
overlap errors at L181-191): two impls of the same trait for the same type in the same
`cfg_group` with different `cfg_arm` are mutually exclusive and do not overlap; impls in
different groups or unguarded impls overlap unless the matrix check proves their guards disjoint.

### Codec ordinals
The codec is positional (`20.hir/hir_definitions.spl:676`; `20.hir/hir_codec.spl:48-84`; generated
files live in `20.hir/generated/`: `hir_codec.spl`, `hir_hash.spl`, `hir_children.spl`, `hir_visit.spl`,
`hir_visitor.spl`).
- Append new fields at the end of each struct's field list; never reorder.
- Option B needs no new `HirExprKind` variant (CfgSelect already landed last).
- Bump `HIR_CODEC_VERSION` once per PR that changes bytes; the header mismatch rejects old cache
  entries (`hir_codec.spl:540`), which is the wanted invalidation.
- `cfg`, `cfg_group` and `cfg_arm` must enter `hir_hash.spl` and `hir_function_record_identity_v1`
  (`20.hir/`, consumed by `40.mono/monomorphize_integration.spl:20`), or two functions differing only
  in guard hash and mono-digest equal.
- Empty `cfg` encodes as a zero-length list. Regenerate the five generated files; no hand edits.

## 2. Non-scoping statement arms (binding chains)

`src/lib/nogc_sync_mut/io/retained_file.spl:197-206`:
```
@when(os="windows"):
val supported = true
@else:
@when(os="linux"):
val supported = true
@else:
val supported = false
@end
@end
if not supported: return Err("SCVDB_FILE_HOST_UNSUPPORTED")
```
`supported` is declared in an arm and read after `@end`. Marker mode turns each arm into a nested
block, so the binding would vanish at block end (`parser_preprocessor.spl:417-420`).

| Option | Mechanism | Verdict |
|---|---|---|
| (a) merged per-arm bindings | `CfgSelect` gains `exports: [HirCfgExport{name, ty, local}]`. HIR resolution declares one `LocalId` per exported name at chain entry; each arm's `val x = e` becomes the initialisation of that local; every arm must give the same type. | Recommended for typing |
| (b) MIR splicing | Arms are non-scoping blocks; MIR splices the selected arm's statements into the parent. Names visible after `@end` need a HIR name table anyway, which is (a). | Use as the MIR realisation of (a) |
| (c) keep flat strip | status quo | fallback during migration |

Rules for (a)+(b):
1. Every arm including `else` that exports `n` must agree on the type of `n`. If an arm omits `n`
   and code after `@end` reads it: `E-CFG-BIND-MISSING` (no implicit nil).
2. No definite-assignment analysis exists in HIR (a search of `src/compiler` finds none), so the rule
   is syntactic: a chain that exports a binding and has no `else` is an error (`E-CFG-BIND-NOELSE`),
   whether or not it is read later. The retained_file shape ends in `@else`, so it is fine. Exports
   propagate through a nested `CfgSelect` in arm position (retained_file's inner windows/linux/else chain
   sits in the outer `@else`): the inner chain's exports count as the outer arm's exports, and the inner
   chain must itself be exhaustive.
3. Exported names are exactly those at the chain's own indent; nested-block bindings stay scoped.
4. MIR lowers only the selected arm, so exactly one initialisation survives and `val`
   single-assignment holds.
5. `_pp_chain_marker_ok` drops its `_pp_starts_binding` rejection; the preprocessor tags
   chain-indent bindings with an `__cfg_export__` marker so HIR does not infer scope from indentation.

Top-level chains (class 2 above) go through section 1: arms contain items whose guards propagate;
a top-level `val` in an arm is a guarded `HirConst`.

## 3. Cache interaction

- HIR cache key: plan step 5 ("Cache keys"; step 4 is MIR lowering, step 6 is typing) removes the target from `hir_cache_key` (`driver_hir_cache.spl:172-187`;
  `_hir_cache_target_context` at `:169-170`, tagged `WA(hir-target-neutral)` by #4908). That is
  sound only when no strip decision remains before parse, otherwise a cross-target hit serves a
  target-stripped AST. So removal is per source file: a file whose preprocessing still made a
  strip decision keeps the target in its key; fully neutral files drop it. Caveat: `_pp_target_record`
  (`parser_preprocessor.spl:374`) records only under `_pp_target_mode`, so on the HIR path every file
  would look neutral. `_pp_preprocess_conditionals` must therefore emit the neutral flag and a decision
  digest unconditionally, independent of `_pp_target_mode`. Add a `hir-cfg-neutral:v1` component so old
  target-specific entries are never reused.
- Neutrality must be closure-wide. `hir_cache_closure_digest` (`driver_hir_cache.spl:143-152`) hashes only
  each surface's path, content hash (raw source, `driver_source_pipeline_loading.spl:1360`), length and
  names. A neutral file importing a non-neutral module would otherwise hit across targets. Add each
  surface's `neutral` flag, or its preprocessor decision digest when non-neutral, to the per-surface
  line (both emitted unconditionally by `_pp_preprocess_conditionals`, see above), so the closure digest changes with the target exactly when some member's HIR would.
- Parse snapshot / TLDR: parse reuse is gated on host os/arch/cpu (`80.driver/managed_parse_group.spl:37`).
  The preprocessor should emit a `neutral: bool` stored with the snapshot; neutral snapshots drop the
  os/arch gate. TLDR module summaries (`module_tldr_registration.spl`) must list guarded symbols with
  their guards, else a TLDR built for one target hides a symbol that exists on another. Bump the TLDR
  schema together with the HIR codec version.
- `_hir_cache_env_switches` (`:154-155`) already folds the flag into the key; keep until the flag is
  deleted in the last migration step.
- Object cache stays target-keyed (`80.driver/driver_build/incremental.spl:674` via
  `cfg_guard_context_identity_v1`); target identity moves from HIR to MIR/object keys, per the plan.

## 4. Migration (small PRs, each red then green)

All behind `SIMPLE_HIR_CFG_SELECT` (extended to declaration mode) until step 8; flat strip is the
fallback throughout, so ordering never breaks bootstrap.

| # | PR | Red spec | Green |
|---|---|---|---|
| 1 | Add `cfg`, `cfg_group` to `HirFunction` only; regenerate codec/hash/children; version bump; no producer | codec round-trip of a function with `cfg=["os=linux"]` fails (field absent) | round-trip and hash differ by guard |
| 2 | Same fields on struct/class/enum/trait/const/impl/import; add `mir_cfg_item_enabled` | MIR keeps a guarded item for matching `MirTargetContext`, drops for mismatch, fatal on malformed | evaluator spec |
| 3 | Guarded `SymbolTable` entries (canonical group id in the five indexes), overlap errors, `E-CFG-SIG-DIVERGE`, guard-aware coherence in `checker.spl` | hand-built HIR (no producer yet): two same-named fns with disjoint guards error today; unguarded+guarded duplicate must error | resolution spec |
| 4 | Preprocessor emits `__cfg_decl__("cond")` for column-0 `@cfg` on fn, flag on | `@cfg(os="windows") fn f` + `@cfg(os="linux") fn f`: HIR contains both; MIR remaps a call by `cfg_group` | lowering fills `cfg`, `cfg_group`, `cfg_arm` |
| 5 | Remaining decl kinds, impl members, guarded `use`, guard-aware import closure | linux build must not load a windows-only import | closure spec |
| 6 | Top-level `@when` chains become guarded items (group + arm index); warning-only for non-selected-arm errors first | module-level chain survives to HIR | per-target MIR item-set spec |
| 7 | Binding-chain exports (section 2), relax `_pp_chain_marker_ok`, `E-CFG-BIND-*` | `retained_file.spl:197-206` shape compiles on windows and linux; missing-else read fails | exports lowered |
| 7b | Flip step 6's non-selected-arm diagnostics from warning to error | a type error in a non-selected arm is only a warning today | error-severity spec |
| 8 | Cache: per-file neutral flag, closure-wide neutral digest, drop target from neutral keys, delete flag and `WA(hir-target-neutral)` | one HIR entry serves two targets for a neutral closure; a neutral file importing a non-neutral module stays target-keyed | key spec |

## 5. Risks

- **Pointer-width-dependent layout.** HIR typing reaches `30.types/_TypeLayout/layout_core.spl:409`
  (`platform_pointer_bit_for_arch`; `platform_cpu_for_arch` is at 389-408). A neutral HIR has no arch, so size/offset queries must run in MIR
  or per variant with an explicit target; `usize`/pointer-sized types stay symbolic in HIR. Layout-using
  `static_asserts` (`HirModule.static_asserts`) move to a MIR-time pass: a behaviour change needing its
  own spec. Guarded struct variants with different field types are fine, each has its own `SymbolId`.
- **Extern availability per target.** A guarded `extern fn` is linkable only on its enabled targets;
  neutral typing must not assume it exists. The unbacked-extern ratchet
  (`scripts/check/check-unbacked-extern-ratchet.shs`) and extern census must read the selected extern
  set per target, or they over-report windows-only externs on Linux.
- **Compile time and memory of typing all variants.** Worst case multiplies typing work by variant
  count (stdlib os/arch chains in `lib/nogc_sync_mut/io/**`, `platform`). Mitigations: lazy variant
  checking with a target set; `cfg_group` allows checking identical `@else` fallback bodies once;
  measure self-compile time and max RSS before and after step 8 and revert on a material regression.
- **New diagnostics from never-compiled arms.** Ship warning-only first (step 6).
- **Seed lane.** The Rust seed has its own preprocessor; the Simple lane keeps flat strip under the
  seed (flag default off) so the lanes do not diverge.
- **Condition grammar drift.** `_pp_eval_condition` and `mir_cfg_select_arm` share only the alias tables
  (`mir_cfg_select.spl:10-11,22-23`, `_pp_os_name/_pp_arch_name`); any new atom needs a parity spec.
  Open gap: `MirTargetContext` folds `armv*`/`thumbv*` to `arm` (`00.common/mir_target_context.spl:56-57`)
  while the preprocessor folds only `armv6/armv7` to `arm` (`_pp_arch_name`, `parser_preprocessor.spl:49`)
  and keeps `thumbv*` and `riscv32` exact; `mir_cfg_select.spl:21-33`
  documents it. The step 5 PR (remaining decl kinds) is in progress and does not close it.

## 6. Open questions

1. Is the os x arch matrix enumeration for cross-chain implication cheap enough, and do any real
   guards use non-os/arch/feature atoms that would need a fourth axis?
2. Accept `E-CFG-SIG-DIVERGE` for unguarded callers, or forbid divergent signatures outright in v1?
3. Default target set for lazy variant checking: build target plus host, or the whole release matrix?
4. A guarded `use` of a module absent on the build target: error, or silent skip when all uses are guarded?
5. Layout-dependent `static_assert` moving to MIR: accept, or keep a target-explicit HIR typing mode?
6. Should binding export be explicit syntax (`@export val x`) rather than inferred from chain indentation?
7. Should an unguarded caller of a group be accepted when the group is exhaustive over the os x arch
   matrix (some arm always applies)? A target-neutral exhaustiveness rule would replace "identical
   signatures" for such callers; a group without `else` that is not exhaustive would be an error.
