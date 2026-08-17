# Deleting the pure-facade glob gate swaps 356 import winners (33 of them types)

- **Date:** 2026-08-01
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  "Resolution (2026-08-01)" at the bottom. Kept OPEN-as-history above so the
  measurement that drove the decision is not lost.
- **Area:** `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`
  (`register_glob_imported_symbols_depth`)
- **Landed in:** `3226faaf9eb`; reverted (gate only) at `b2d42b02ecc`+1
- **Severity:** MEDIUM — no observed miscompile, but type identity moves.

## Background

`3226faaf9eb` bundled **two** changes under one "memoize nested glob expansion"
headline:

- **(A) the memo** — `glob_expand_memo: {text: i64}`, skip re-expansion of a
  module key already expanded at the same or shallower depth.
- **(B) the ungate** — deletion of the `facade_shape` guard, so nested glob
  recursion now happens for *every* globbed module, not only pure facades.

(B) is a reachability change, not an optimisation. It is the semantically
load-bearing half, and the commit headline does not say so.

## Why an unresolved-name census cannot see this

`SymbolTable.define` (`src/compiler/20.hir/hir_types.spl:246`) is **not**
uniformly first-wins:

- `Class` / `Struct` / `Enum` / `Trait` → first-write-wins (returns existing id)
- **everything else (Function, Const, TypeAlias) → allocates a fresh id and runs
  `scope_syms[name] = raw_id`, i.e. last-write-wins**

So when two reachable modules provide the same name, changing the walk changes
*which module wins* — but the name still resolves. **A swapped winner produces
no `unresolved` line.** The subset gate (patched unresolved set ⊆ pristine) is
blind to it by construction, and it passed precisely because nothing was lost.

## Measurement (PROVED by simulation over the real graph)

Faithful port of `hir_module_logical_name_from_path`, `resolve_module_key`,
`resolve_module_key_relative` and the parser rule that `use a.b.c` with no braces
or star is a **glob**. 13,828 modules, 29,643 `use` edges (8,204 glob / 21,439
named), resolver hit rate 85.2% overall / 77.6% glob. 3,552 roots with ≥1
resolvable glob import. Misses are dominated by module paths absent from the tree
(`compiler.core.ast` ×323 etc.), which the real compiler also fails to resolve.

Four walks were simulated: pristine (gated, no memo), patched (ungated + memo),
ungate-only, memo-only.

| metric | value |
|---|---|
| **LOST** (resolved before, unresolved after) | **0 — in every variant** |
| **SWAPPED** (resolves in both, different winner) | **356 pairs / 164 names / 97 roots (2.7%)** |
| — of which TYPE (first-wins) | 33 |
| — of which VALUE (last-wins) | 323 |
| NEWLY RESOLVED | 132,691 pairs / 11,105 names |

`LOST = 0` is the reason the landed change is safe against the stated gate, and
it is structural, not luck: the memo prunes only re-entries at a depth ≥ a prior
visit, whose expansion was a superset of what the pruned one would add.

### Isolating the two halves — this is the finding

| variant | swaps | newly | lost | expansions (3,552 roots) |
|---|---|---|---|---|
| pristine (gated, no memo) | — | — | — | 27,445 |
| **memo-only (gate kept)** | **0** | **0** | **0** | 9,133 (0.33×) |
| ungate-only (no memo) | 345 | — | 0 | 2,618,811 (**95×**) |
| **patched (ungate + memo, as landed)** | **356** | 132,691 | **0** | 34,972 (**1.27×**) |

**All winner-changing damage comes from the ungate (B), not the memo (A).** The
memo alone is behaviour-identical to pristine and 3× cheaper — it is free. The
memo adds only 32 further swaps on top of the ungate, all last-wins ordering
flips.

### Example type swaps (the ones that matter)

| name | pristine winner | patched winner |
|---|---|---|
| `BlockId` | `backend.backend.mir_test_builder_full` | `mir.mir_instruction_support` |
| `CompiledModule` | `backend.codegen` | `backend.backend.backend_types` |
| `LineContext` | `tools.fix.rules.helpers` | `lib…tooling.easy_fix.rules_helpers` |
| `DuplicateTypedArgSignature` | `tools.fix.rules.impl_.lint_code` | `lib…tooling.easy_fix.rules` |

`BlockId` and `CompiledModule` changing defining module changes **type identity**
inside `compiler.backend`.

## The 52× figure in the commit message is wrong for what landed

The commit cites "394,207 expansions vs 7,529 — 52×" as the memo's justification.
That ratio describes the **un-memoized ungated** shape (measured here as 95×),
not the landed patch. Against the actual pristine baseline the landed change is
**1.27× more expensive**, not 52× cheaper: median per-root ratio 1.0, p90 4.7,
max 251 (`app.editor.editor_controller`). The memo's real job is to make the
ungate affordable (2.6M → 35k), which is a correct and necessary role — but it
is not a speedup over pristine, and the commit message reads as though it were.

## Caveats

- The root module's own declarations are not modelled; they shadow imports, so a
  listed swap is only a live defect where the root does not itself declare the
  name. (INFERRED)
- Indexing every symlink spelling over-approximates the real single-spelling
  registry, so 356 is an upper bound. (INFERRED)
- Stage3 builds clean on both arms (728/0/0) and the produced binaries run, so no
  swap has been shown to miscompile anything. (PROVED — absence of observed harm,
  not proof of harmlessness.)

## Recommended follow-up

1. Decide deliberately whether the ungate is wanted. It was justified by
   `MirOperand`/`MirType` leakage (`mir_data.spl:19` does
   `use compiler.mir.mir_types.*`; **101** modules glob-import `mir_data`), and
   the simulation confirms the intended benefit is real — `MirOperand` 3→165
   roots, `MirType` 9→166. But **neither symbol was ever unresolved at this
   tip**, so the ungate is not fixing an observed failure while it does move 33
   type winners.
2. If the ungate is kept, add a lint/assert that flags a glob-provided name
   supplied by two distinct modules reachable from one root, so future winner
   swaps are loud rather than silent.
3. Correct the 52× claim wherever it is quoted.

## The `Function` / `Const` slice: INERT on every normal lane, OBSERVABLE only under the entry-closure bootstrap

Closes the half the `TypeAlias` note explicitly excluded. Measured at tree
109,562 (`f93c9b26232`), simulation re-run and reproduced exactly: 356 swaps,
of which **280 `callables` + 43 `constants` = 323 Function/Const rows**, 160
distinct (name, providerA, providerB) pairs over 155 names. Glob expansion does
register both categories (`register_glob_imported_symbols_depth`,
`module_lowering.spl:943` callables, `:955` constants), so these are real, not a
simulation artifact.

### Divergence is real and large — that is NOT what makes it safe

Of the 160 Function/Const provider pairs, comparing the two providers' actual
source definitions: **99 genuinely diverge** (75 differing bodies, 24 differing
signatures); 61 are byte-identical. This is a far higher divergence rate than the
`TypeAlias` slice (7 of 52). Worst examples:

| name | provider A | provider B |
|---|---|---|
| `LOG_TRACE` | `lib.nogc_sync_mut.log` = **6** | `lib.log` = **0** |
| `LOG_INFO` | `lib.nogc_sync_mut.log` = **4** | `lib.log` = **2** |
| `LOG_ERROR` | `lib.nogc_sync_mut.log` = **2** | `lib.log` = **4** |
| `LOG_OFF` | `lib.nogc_sync_mut.log` = **0** | `lib.log` = **6** |
| `_entry` | `wine_nt_dispatch_table` `(symbol, dll, category, implemented: bool) -> NtDispatchEntry` | `wine_nt_api_catalog` `(dll, symbol, category, state: text) -> WineNtApiCatalogEntry` |
| `_md_parse_i64` | `md_language` `(value: text) -> i64` | `md_editing` `(raw: text, fallback: i64) -> i64` |

The two `log` modules use flatly contradictory, near-reversed numbering. If the
winner were observable this would be a live miscompile. It is not observable —
for the reason below, not because the definitions agree.

### Why it is inert (PROVED — four independent proofs, `/usr/bin/grep` pinned)

Two competing import registrations of the same name are created by the SAME call
(`register_imported_symbol`, `module_lowering.spl:601`) with the SAME arguments
except the source surface. Field by field, the resulting `HirSymbol`s differ in
**exactly one place**: `defining_module`. (`name` = `local_name`, `kind`,
`visibility` = `Public`, `is_mutable` = `false` are literals; `span` is the
import statement's, diagnostics only.)

1. **`type_` is `nil` for both candidates, always.** `declared_surface_callable_type`
   returns `nil` when `registering_import_symbols` is set
   (`module_lowering.spl:359-360`), and that flag wraps the entire import pass
   (`:1350-1353`). So the Function registration at `:635` stores `nil`. The Const
   registration at `:638` passes a `nil` literal. Same shape as `TypeAlias`.
   The prior lane's refuted ordering-fix observation applies here directly: import
   registration lowers no signatures at all.

2. **`defining_module` — the only differing field — has ZERO Function/Const readers.**
   `/usr/bin/grep -rn "\.defining_module" src/compiler/` (excluding the
   constructor keyword `defining_module:`) yields exactly five reader sites, and
   every one is unreachable for a Function or Const symbol:

       vhdl_design_catalog.spl:368   guarded by `case Struct | Enum:`      (:366-370)
       vhdl_design_catalog.spl:381   guarded by `case Variable:`            (:379-383)
       50.mir/_MirLowering/module_lowering.spl:166  composite_layout_key -- all six
           callers (:541 :552 :575 :604 :615 :825) obtain the symbol from
           struct_def.symbol / class_def.symbol / a HirTypeKind.Named payload
       50.mir/_MirLowering/module_lowering.spl:176  canonical_mir_type_symbol -- type ids only
       35.semantics/value_struct_layout.spl:74      struct layout
       20.hir/hir_types.spl:475                     method_symbol_name(type_id, ...)

   Not one is reached by a name lookup that could return a Function or Const.

3. **Every consumer of a looked-up Function symbol reduces it to `sym.name`, and
   `sym.name` is identical for both candidates.** MIR emits a call as a NAME
   STRING, not a symbol id: `switch_operators_calls.spl:3711-3721` builds
   `MirOperand ... MirConstValue.Str(resolved_name)` where
   `resolved_name = direct_name` carried on `HirExprKind.NamedVar(symbol, name)`,
   baked at HIR lowering by `symbol_display_name` (`hir_types.spl:394-398`,
   returns `sym.name`). The symbol-id fallback `bootstrap_resolved_call_name`
   (`switch_operators_calls.spl:976`) also returns `found_sym.name`; so does
   `const_eval.spl:376-378`. Since `register_imported_symbol` defines every
   candidate under the same `local_name`, the emitted string is the same
   whichever provider wins. Which body actually answers that string is decided by
   the flat name registry — the pre-existing bare-name collision — and the swap
   does not move it.

4. **An imported `Const` is never materialized.** `register_imported_symbol`
   copies enum bodies (`imported_enums`, `:623`) and trait bodies
   (`imported_traits`, `:629`), but for `constants` (`:637-638`) it stores only a
   nil-typed symbol; there is no `imported_constants` map anywhere (`grep` = 0
   hits). `global_symbol_ids` / `global_const_exprs` / `module.constants` are
   keyed by the DECLARATION's `const_.symbol.id`
   (`50.mir/_MirLowering/function_lowering.spl:512-522`), never by an import id,
   so `try_lower_global_read` (`expr_dispatch.spl:169`) returns `nil` for both
   candidates identically. The `LOG_*` value contradictions above therefore
   cannot reach codegen through this mechanism.

Lanes covered: interpreter, JIT and native — the argument is at HIR/MIR
lowering, upstream of all three.

### The one exception: `qualify_imported_function_symbol` (PROVED mechanism)

`qualify_imported_function_symbol` (`module_lowering.spl:880-900`) calls
`rename_symbol(sym_id, "{imported_mod_name}.{imported_name}")` — but **only**
when `SIMPLE_BOOTSTRAP=1` AND `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1`. On that lane
`sym.name` becomes provider-dependent, and by proof 3 that string IS the emitted
callee. Because `Function` is last-write-wins, the scope binding always points at
the last registration, so the rename lands on the winner: a swap redirects the
call from `{A}.foo` to `{B}.foo`, i.e. to the other provider's body.

Exposure: **239 of the 323 Function/Const swap rows are divergent**, over 52
distinct roots — 153 `lib.*`, 72 `compiler.*`, 14 `app.*`. The `compiler.*` roots
are `compiler.driver.driver`, `compiler.frontend.flat_ast_bridge`,
`compiler.loader.loader.module_loader`,
`compiler.loader.loader.module_loader_lib_support`,
`compiler.tools.fix.rules.impl_.impl`, `compiler.tools.fix.rules.registry` — i.e.
modules that are inside the bootstrap closure. `Const` is unaffected even here
(`:638` never calls `qualify_imported_function_symbol`).

No miscompile has been observed on that lane; stage3 built clean on both arms per
the measurement above. The mechanism is PROVED; a resulting defect is INFERRED
and unobserved.

### Consequences for the standing "is the ungate wanted" decision

Stated plainly, as requested:

- The memo (A) causes **0** swaps, is behaviour-identical to pristine, and is 3x
  cheaper. It is free and should be kept.
- The ungate (B) causes **345 of the 356** swaps and its stated justification
  (`MirOperand` / `MirType` leakage) was **never an observed failure** — neither
  symbol was unresolved at this tip.
- On every normal lane the Function/Const half of that cost is provably zero.
  The residual cost is the 33 TYPE swaps (already documented above, first-wins,
  they move type identity) plus the entry-closure Function exposure just
  described — which lands on the bootstrap's own driver and loader modules.
- **Recommendation: revert the ungate, keep the memo.** It buys no measured fix,
  and its only measurable effects are winner swaps — two classes of which are
  observable. This is a decision for the owner; nothing has been reverted here.

**Not fixed, deliberately.** Making `Function`/`Const` first-write-wins was
considered and rejected: `define`'s last-wins branch is what makes shadowing and
overloading work (`hir_types.spl:254-255`), so flipping it is a far larger
semantic change than the defect it would close.

### Reproduction

`/dev/shm/globsim/sim_fable.py` (sim.py + a Function/Const categoriser) and
`diverge.py` (provider-definition differ). Outputs `fable_swaps_full.json`,
`fable_fnconst_pairs.json`, `fable_divergence.json`. Scratch, not durable.

## Artifacts

Simulation sources and full result sets: `/dev/shm/globsim/` (`extract.py`,
`sim.py`, `detail.py`, `report.json`, `detail.json`) — scratch, not durable.
Patch and run wrappers: `build/glob-memo-lane-artifacts/`.


---

## Resolution (2026-08-01) — gate restored, memo retained

The two halves of `3226faaf9eb` were separated and only **(B) the ungate** was
reverted. **(A) the memo** (`glob_expand_memo` in `hir_lowering/types.spl` plus
the check/insert and per-root reset in `module_lowering.spl`) is **kept**.

Source delta is 4 non-comment lines: re-add `has_own_symbols` / `facade_shape`,
and restore `if glob_imp.items.len() == 0 and facade_shape:`.

### Acceptance evidence

Simulation re-run against the **exact** origin tip `b2d42b02ecc` (graph
re-extracted from that tree: 13,801 modules, 22,717 spellings, 3,553 roots with
at least one resolved glob import). Baseline `pristine` = gated + un-memoized =
the pre-`3226faaf9eb` walk.

| arm | gate | memo | expansions | swaps | type swaps | newly | lost |
|---|---|---|---|---|---|---|---|
| pristine (pre-3226) | ON | off | 27,445 | — | — | — | — |
| patched (3226 as landed) | off | ON | 34,973 | **356** | 33 | 132,687 | 0 |
| ungate_only | off | off | 2,618,812 | 345 | 33 | 132,221 | 0 |
| **memo_only (THIS CHANGE)** | **ON** | **ON** | **9,133** | **0** | **0** | **0** | **0** |

- **PROVED — the swaps go away completely.** Not the ~11 residue that was
  predicted: gate-plus-memo reproduces the pre-`3226faaf9eb` import-winner map
  **exactly**, 0 swaps / 0 newly / 0 lost across all 3,553 roots. The memo is
  observationally inert once the gate is back.
- **PROVED — the memo still pays.** 27,445 -> 9,133 expansions, a 3.0x
  reduction, with zero winner change. It is free and it is kept.
- **PROVED — the ungate was the whole cost.** Un-gated and un-memoized the walk
  costs 2,618,812 expansions (95x the gated baseline) and hits the depth cap on
  one root. Gated, the depth-8 cap alone already terminates with 0 capped roots.

  Correction to the original commit message, which called the memo load-bearing
  for termination: **in the gated configuration it is not.** The gate terminates
  on its own; the memo is a 3x saving and a margin against the cyclic glob graph
  (168 directed 2-cycles over 3,026 `use x.*` edges). Un-gated it *is*
  load-bearing — that is why the two must move together if the gate is ever
  lifted again.

### No regression: seed -> stage2, four arms at the same tip

`simple_seed native-build --entry-closure --mode dynload --backend llvm`, same
flags as `bootstrap-from-scratch.sh` stage 2, in a dedicated tree at
`b2d42b02ecc`:

| arm | result |
|---|---|
| pristine (tip, ungated) | 728/728 compiled, 0 cached, **0 failed**, 91.6s |
| pristine2 (identical re-run, determinism control) | 728/728, **0 failed**, 123.3s |
| patched (gate restored) | 728/728, **0 failed**, 99.2s |
| final (exact landed bytes) | 728/728, **0 failed**, 88.6s |

**Sets, not counts.** The content-addressed compile cache is the deterministic
per-unit set:

- control (pristine vs pristine2, identical source): **0 of 729** cache entries
  differ.
- pristine vs the landed bytes: **exactly 1 of 729** entries differs — the
  `module_lowering` unit itself, the only file edited.

Raw `.o` files are **not** reproducible and must not be used as the set signal:
the same source compiled twice produced 7 byte-differing objects and 14 changed
object hashes. That noise floor is why the cache set, not the object set, is the
gate.

Link fails identically (byte-identical error text, md5 `9ad95fc2...`) in **all
four** arms on `rt_native_build` / `rt_cranelift_*` / `max`. That is an artifact
of the ad-hoc runtime authority used for this comparison, not of the change; it
is present in the unmodified-tip arm.

### Signals deliberately NOT used

- **stage4 unresolved counts.** stage4 exits 1 at `[ERROR] phase 3 FAILED` —
  phase 3 *is* HIR lowering — with 6,474 `[stmt_get_tag] OOB` / `arena_len=0`
  events, the first on log line 1. Its zero counts are early-abort artifacts.
- **stage3.** It runs the bootstrap-flat pipeline and never performs this
  lowering at all.

### On the stated justification for the ungate

It does not hold. `MirOperand` / `MirType` were never an observed failure at
this tip, and `MirType` remained unresolved x77 in the patched stage4 arm. The
ungate did not achieve its goal, and its only measurable effects are the winner
swaps documented above — including 33 that move TYPE identity (`BlockId`,
`CompiledModule` inside `compiler.backend`) and, under `SIMPLE_BOOTSTRAP=1` plus
`SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1`, the `qualify_imported_function_symbol`
rename that makes the winner the emitted callee (239 divergent rows over 52
roots, including `driver.driver` and `loader.module_loader`).

The `Function`/`Const` and `TypeAlias` slices remain **inert**, as previously
proved. They are not a reason for this revert and are not restated as harms.

### Reproduction of the resolution measurement

`extract.py` + `sim_fable.py` re-pointed at a `git archive` of `b2d42b02ecc`;
the arm table is printed by the appended `VERDICT=` block. Scratch, not durable.
