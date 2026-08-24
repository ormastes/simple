# Duplicate compiler module trees REFUTED; spurious ambiguity is a re-export hop item_name defect

- **Date:** 2026-08-24
- **Lane:** E4 (Stage 3 self-host blocker, cross-cutting hypothesis)
- **Status:** OPEN — root cause localized, fix NOT landed (needs a stage2 rebuild to instrument)
- **Area:** `src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl`
  (`find_reexport_source_walk`), feeding
  `materialize_imported_callable_explicit_dependency_inner`'s ambiguity sweep
- **Severity:** MEDIUM (4 of 405 stage-3 HIR fatals directly; unquantified spillover
  into the first-match-wins facade chase)

## Part 1 — the duplicate-module-tree hypothesis is REFUTED

The hypothesis was that `src/compiler/backend/**` and `src/compiler/70.backend/**`
(and the 16 sibling pairs) are two trees on disk, and that the resolver registers
each file twice under two module IDs, producing `ambiguous` verdicts and
cross-copy field invisibility.

Two independent disproofs:

1. **They are symlinks, not copies.** All 17 unnumbered directory names under
   `src/compiler/` are symlinks to their numbered counterparts:

   ```
   backend -> 70.backend    hir -> 20.hir       loader -> 99.loader
   frontend -> 10.frontend  common -> 00.common ... (17 total)
   ```

   There is exactly ONE physical copy of every compiler source file. Of the 609
   distinct `src/compiler/**` paths named in `/mnt/data/goal-logs/stage3-failure.log`,
   608 distinct realpaths — a single path pair (`elf_writer.spl`) is spelled both
   ways, and even that is one file.

2. **Both spellings normalize to ONE module ID.** Compiling
   `src/compiler/backend/linker/link.spl` (unnumbered spelling) yields owner
   `compiler.backend.linker.link`; the 2026-08-22 record shows
   `src/compiler/70.backend/backend/llvm_backend.spl` (numbered spelling) yielding
   `compiler.backend.backend.env`. Numbered and unnumbered paths land on the same
   module name. No dual registration exists in `module_surfaces.surfaces`.

**Consequence for sibling lanes:** the duplicate-tree mechanism explains **0 of the
405** HIR lowering errors. Lanes E, E2 and E3 should stop attributing their clusters
to it. (The `aspect_dynload` lane plan's "duplicate modules are the mechanism"
finding refers to genuinely duplicated *loader* sources elsewhere, not to these
symlinked compiler directories.)

## Part 2 — what the ambiguity actually is

### Cheap reproducer (no bootstrap; ~minutes)

```sh
export SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_AMBIGDBG=1
STAGE2=<goal-stage2>/stage2/x86_64-unknown-linux-gnu/simple
$STAGE2 compile --format=smf -o /tmp/link.smf src/compiler/backend/linker/link.spl \
  > /tmp/link.out 2> /tmp/link.err
rc=$?
```

`rc=139`. Note the SEGV is a *separate* observation — it follows the fatals and is
consistent with the known stage-binary SEGV class
(`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`); it is not
chased here. Before the SEGV the run reproduces the fatals faithfully, including
the two the whole-tree stage-3 log reports for this file.

### The evidence

`SIMPLE_AMBIGDBG=1` prints every candidate the sweep considers. For `DiContainer`:

```
sweep-candidate route=glob owner=compiler.backend.linker.linker_context \
    dep=DiContainer import=1 target=compiler.common.di item=DiContainer
sweep-candidate route=glob owner=compiler.backend.linker.linker_context \
    dep=DiContainer import=3 target=compiler.common.di item=compiler.common.di
sweep-verdict ... dep=DiContainer ambiguous=true
```

Both candidates name the **same target module**. `DiContainer` has exactly ONE
declaration in the whole tree (`src/compiler/00.common/di.spl`). The candidates
differ only in the ITEM slot, where the second carries the *target module's own
name* instead of the item name. The sweep compares
`selected_item != candidate_item` and therefore declares ambiguity.

This is not a two-owner collision (unlike the `Backend` case in
`ambiguous_explicit_callable_dependency_backend_env_2026-08-22.md`, which was
genuine and was correctly fixed by explicit-over-glob precedence). It is a
**spurious** ambiguity over a single owner.

### It is universal, not anecdotal

Across the whole `link.spl` compile, of the 35 dependencies that produced more
than one sweep candidate:

| property | count |
|---|---|
| multi-candidate dependencies | 35 |
| ...where ALL candidates share one target | **35 / 35** |
| ...carrying a candidate whose `item` == the target module name | **35 / 35** |

Zero counterexamples. Every multi-candidate case in the run has this exact shape.

### Where the corrupt item comes from

The bad candidate is produced by the hop, not by the sweep:

```
chase mod=compiler.backend.linker.linker_context wanted=DiContainer \
    found=true target=compiler.common.di item=compiler.common.di
chase mod=compiler.backend.linker.linker_context wanted=DiContainer \
    found=true target=compiler.common.di item=DiContainer
```

`find_reexport_source` itself returns `item_name` = a module name. Its six
`found: true` return sites yield `wanted`, `source_item`
(`facade_mod.import_item_names[...]`), `exp_source`
(`facade_mod.export_route_sources[...]`), or `origin_lookup.source_name`
(the export-origin index). None of these should ever hold a module name, so one
of those surface arrays is being populated with one upstream — most likely for the
brace-less dotted import form, which is exactly how the two failing deps in
`linker_context.spl` are written:

```
use compiler.common.di.DiContainer     # not `...di.{DiContainer}`
use compiler.tools.aop.AopWeaver
```

Both other deps in the same run with this defect (`SmfReaderImpl`, `SmfSymbol`,
`Type`) show the identical candidate shape.

## Why no fix is landed here

The fix belongs upstream, at whichever surface-builder site writes a module name
into an item slot. Identifying it needs a trace inside
`find_reexport_source_walk` — and **the stage2 binary is prebuilt, so editing
`src/compiler/**` does not change its behaviour**; confirming the site requires a
stage2 rebuild (hours). That work is handed off rather than guessed at.

A sweep-side dedupe ("same target, prefer `item == dependency`") is explicitly
**rejected** as the fix: the same hop machinery also feeds
`register_imported_symbol_inner`'s first-match-wins facade chase, where a corrupt
`item_name` does not say "ambiguous" — it silently binds the wrong symbol. Masking
it in the sweep would leave that silent path intact. That path is a plausible
mechanism for part of the 207 `unresolved name` errors reported at `use`-line
columns, so the upstream fix may clear materially more than the 4 ambiguity
errors.

Note also `expression_support.spl:392-402`, which records that a previous
permissive change in this area drove `ambiguous explicit callable dependency` from
4 to **447** and total fatals from 312 to ~6517. Changes here must be measured on a
real whole-tree run, never on a small fixture.

## Error-class accounting (stage-3 log, 405 fatals)

| class | count | explained by duplicate trees | explained by this defect |
|---|---|---|---|
| unresolved name | 207 | 0 | unknown (possible, via the silent facade chase) |
| field not visible | 152 | 0 | no |
| unresolved type | 42 | 0 | plausible downstream (see the `selected_target < 0` comment) |
| ambiguous explicit callable dependency | 4 | 0 | **yes, all 4** |

---

# CORRECTION (same day, after coordinator evidence): verdict is PARTIAL, not REFUTED

Part 1 above refutes only the shape I censused — the **numbered/unnumbered symlink
alias pairs**. That refutation stands and is unchanged. But it was scoped too
narrowly: a **second, genuine duplication shape exists**, and it is the likely
cause of the largest error class.

## The real duplicate population

Censused over PHYSICAL files only (`os.walk(followlinks=False)`, symlinked dirs
pruned, so no symlink double-counting): **1815** `.spl` files under `src/compiler`,
**81** duplicate basenames. Classifying rather than assuming:

| class | count |
|---|---|
| duplicate basenames | 81 |
| byte-identical | 1 |
| drifted | 80 |
| **drifted AND declaring at least one same-named type** | **8** |

So 81 is a large overestimate of the actionable population; the systemic set is **8**:

```
object_mapper.spl     8 shared types  (JitMapper, JitMapperConfig, LoaderMapper, …)
jit_instantiator.spl  7 shared types  (JitInstantiator, JitInstantiatorConfig, JitStats, …)
smf_cache.spl         3 shared types  (SmfCache, MappedSmf, CacheStats)
object_provider.spl   2 shared types  (ObjectProvider, ObjectProviderConfig)
diagnostic.spl / lexer_types.spl / desugar_async.spl / jit_context.spl   1 each
```

Five of the eight are the loader cluster. The shape is a nested sub-tree, **not** a
numbered/unnumbered pair — both copies live under the numbered package:

```
src/compiler/99.loader/jit_instantiator.spl         470 lines  sha=64182fc65327  "Compatibility JIT instantiator surface"
src/compiler/99.loader/loader/jit_instantiator.spl  541 lines  sha=d1647e9e6263  "JIT instantiation at load-time"
```

Distinct realpaths, drifted, and **both live** (both write a `.jit.note.sdn`
sidecar). Module names `compiler.loader.jit_instantiator` vs
`compiler.loader.loader.jit_instantiator`.

## Mechanism for the 152 field-visibility errors — name-keyed collision

The initially attractive explanation ("the importer resolved to a copy that lacks
the field") is **wrong, and was checked**: all nine failing fields
(`in_progress`, `exec_mapper`, `jit_semantic_keys`, `loaded_metadata`, `depth`,
`config`, `jit_cache`, `smf_semantic_keys`, `compile_count`) are declared in
**both** copies.

What actually differs is the *declaration kind and field types*:

| | `99.loader/` (compat, 470) | `99.loader/loader/` (541) |
|---|---|---|
| kind | `class JitInstantiator` | `struct JitInstantiator` |
| `in_progress` | `[text]` | `Set<text>` |
| `jit_cache` | `Dict<text, JitCacheRecord>` | `Dict<text, ([u8], i64)>` |
| `exec_mapper` | `JitExecMapper` | `SharedExecMapper` |

And the field-visibility map is keyed by the **bare type name**:

```
module_callable_types.spl:67   self.struct_field_access_by_name[hir_struct.name] = field_access
module_callable_types.spl:49   self.struct_field_access_by_name[name] = field_access
expression_support.spl:309     val fields = self.struct_field_access_by_name[composite_name]
```

A name-keyed map cannot distinguish two same-named composites from different
modules. With both `JitInstantiator` declarations in one whole-tree build, the
second write **overwrites** the first, and every field read against the losing
declaration resolves through the winner's field set — yielding the observed
*whole-field-set* invisibility rather than a single missing field. This is the
same "symbol-id aliasing" family already documented at
`expression_support.spl:384-390`.

This also explains why the error is **build-context dependent**: it needs both
copies present in one compilation.

**Evidence status — stated honestly.** The isolated single-file compile of
`src/compiler/loader/jit_instantiator.spl` emitted **0** field-visibility errors
versus 83 in the whole-tree run, which is consistent with the mechanism, but the
run **SEGV'd (rc=139) during `hir 0/1 ... compiler.loader.jit_instantiator`** — it
did not complete HIR, so that is *not* a clean negative and must not be quoted as
proof. The structural evidence (two same-named composites + a bare-name-keyed
visibility map) is the load-bearing part; a clean empirical confirmation needs a
whole-tree run with one copy renamed.

## Revised error-class accounting

| class | count | duplicate-module explanation |
|---|---|---|
| unresolved name | 207 | unknown |
| field not visible | 152 | **likely — 83 in `jit_instantiator.spl` alone; `hir_codec.spl` (62) needs the same check** |
| unresolved type | 42 | plausible downstream |
| ambiguous explicit callable dependency | 4 | **no** — spurious hop `item_name`, see Part 2 |

## What sibling lanes should do

- **E2 (field visibility):** do NOT patch per-file. Check whether `hir_codec.spl`'s
  62 errors are a same-named-composite collision from the 8-file list. If so, E2's
  and this defect are one root cause.
- **E3 / E:** the symlink alias pairs are still a dead end. The live duplication is
  the 8 same-basename drifted files above.
- **Fix direction (not landed):** either make `struct_field_access_by_name`
  module-qualified rather than bare-name-keyed (the general fix, but it is in the
  hot path the file's own comments warn cost 20x when perturbed), or de-duplicate
  the 8 colliding declarations. Neither should be attempted without a whole-tree
  measurement — a small fixture cannot reach this path.

---

# FINAL SCOPE (after coordinator correction) — duplication explains ONE file, not the class

The "81 duplicate basenames" figure is noise and must not be used: `__init__.spl`
alone contributes 161 paths, and every package legitimately has one. The census in
the CORRECTION section above already avoided that trap by requiring *drifted AND a
shared declared type name* (8 files, not 81). Two of the coordinator's candidates
fail even that stricter test, checked here:

- **`codegen.spl` — NOT a duplicate.** The three files
  (`70.backend/backend/common/codegen.spl`, `70.backend/codegen.spl`,
  `70.backend/irdsl/codegen.spl`) declare `{Codegen, CodegenOutput,
  CodegenOutputKind}`, `{CodegenError, CodegenMode, CodegenPipeline, Cranelift*}`
  and `{IrCodeGen}` respectively — **pairwise shared type names: ZERO**. Three
  legitimately distinct modules that share a basename.
- **`hir_codec.spl` — NOT a duplicate.** `20.hir/hir_codec.spl` (109 lines, 1 type,
  6 fns) and `20.hir/generated/hir_codec.spl` (6856 lines, 0 types, 190 fns) share
  **zero** type names and **zero** function names. It is a hand-written facade over
  a generated implementation, which is the intended arrangement. E2's 62 errors are
  **not** a duplication case.

**Net verdict: the duplicate-module mechanism explains exactly one failing file,
`jit_instantiator.spl` (83 of 405 errors, 20%).** It does not explain the other 30
failing files or the remaining ~322 errors.

## Release notice for sibling lanes

- **E (unresolved names, 207):** duplication is NOT your cause. Proceed
  independently. The one thing worth watching is the silent wrong-symbol bind in
  `register_imported_symbol_inner`'s facade chase (Part 2) — that *can* surface as
  an unresolved name at a `use` line column.
- **E2 (field visibility, 152):** `hir_codec.spl` (62) is refuted as duplication —
  pursue your own root cause. Only the `jit_instantiator.spl` share (83) is mine.
  Note the general hazard regardless of cause: `struct_field_access_by_name` is
  keyed by bare type name, so ANY two same-named composites in one build collide.
- **E3 (backend/frontend/mir_opt/types):** duplication is NOT your cause;
  `codegen.spl` is refuted above. Proceed independently.
