# Deleting the pure-facade glob gate swaps 356 import winners (33 of them types)

- **Date:** 2026-08-01
- **Status:** OPEN — measured, not fixed. The landed change is **not** being
  reverted: it introduces no unresolved-name regression. This documents a silent
  semantic change that no unresolved-name census can detect.
- **Area:** `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`
  (`register_glob_imported_symbols_depth`)
- **Landed in:** `3226faaf9eb`; still live at `f793418c802`
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

## Artifacts

Simulation sources and full result sets: `/dev/shm/globsim/` (`extract.py`,
`sim.py`, `detail.py`, `report.json`, `detail.json`) — scratch, not durable.
Patch and run wrappers: `build/glob-memo-lane-artifacts/`.
