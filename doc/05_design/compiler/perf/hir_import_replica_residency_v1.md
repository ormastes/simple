# HIR residency is dominated by per-importer replicas of imported declarations

Status (2026-11-14): attribution measured on the run-32 HIR cache; step 1
(identity-only `imported_layouts` rows) landed in source with specs; steps 2-4
are design only. No native before/after exists yet: every RSS figure for a
change below is an **estimate** until a Stage 2 built from this source runs.

Related: `mir_shard_hir_residency_v1.md` (interface-only HIR for unclaimed
modules, opt-in), `per_module_stream_to_object_v1.md` (post-mono batching),
`../memory/build_session_memory_model_v1.md` (session heap, no per-module free),
`doc/08_tracking/bug/stage2_compiler_cli_build_mir_shard_share_unbounded_2026-11-06.md`.

## 1. The numbers to explain

Run 32 (source `2864bc90f8c`, aarch64 Linux, 121 GiB), full CLI build
(`src/app/cli/_CliMain/main_and_help.spl`, 3145 modules), one process,
streaming-surfaces route, cold (`cached=0`, 3136 HIR cache stores):

| point | elapsed | top process RSS | source |
|---|---|---|---|
| process start | 0 s | 1.6 GiB | `bootstrap-progress.log` `top_pid=10380` |
| HIR phase starts (sources, parse, surfaces done) | 594 s | ~4.6 GiB | `[build] phase=hir done=0` + RSS samples at 451 s (3.1) / 691 s (4.6) |
| HIR 3145/3145, MIR setup starts | 5300 s | 23.2 GiB | last sample before the kill |

So: **1.46 MB per module before HIR, 5.9 MB per module added by HIR**
(18.5 GiB / 3145). The "7.7 MB per module" figure is the total divided by the
module count. Growth is linear through the whole phase (one sample per 30 s);
no memory snapshot trace was produced (`trace.tsv` absent, `SIMPLE_MEM_SNAPSHOT_FILE`
unset for the row).

Stage 3 of the same run (1664 modules, retained route): MIR worker 5.3 GiB
after load, ~14 GiB after HIR (5.2 MB per module, cold: the pool's entries
were unreadable, fixed by `70d966fce09`), 18.5 GiB at MIR 1600/1664.
`70d966fce09` removes the ~20 minute HIR redo; it is not shown to reduce the
resident HIR, because a cache hit promotes the decoded module in full.

## 2. What the retained HIR consists of (measured)

Method: the run-32 HIR cache of that build holds one entry per module (3145
files, 2353 MB, **766 KB per module**). The codec writes one field per line
and `hir_module_decode` allocates one object or word per field without
sharing, so the encoded field count is the resident size of a **cache-hit**
load and an upper bound for a cold lowering (which keeps pointer sharing).
A systematic sample (every 100th entry by size, 31 entries, 23.1 MB = 0.98 %
of the bytes, 4.9 M fields) was walked with the generated decoder on the seed
(`build/memwork/hir_entry_probe3.spl`, ad hoc); 30 of 31 entries aligned and
are counted below.

| part of `HirModule` | share of encoded fields | per module | later reader |
|---|---|---|---|
| `symbols.symbols` rows of **imported** declarations | 33.3 % | 926 rows, 57 fields each (71 % are functions/methods with full types) | HIR lowering of this module; MIR lowering of this module resolves calls and types through them |
| `imported_layouts` (field copies of imported structs) | **30.0 %** | 165 rows, 1200 fields, ~33 codec fields per field | **none**: the lint `hir_frontend_type_unresolved` reads key membership only |
| `functions` (signatures and bodies of the module's own code) | 15.5 % | 15 functions | MIR lowering of this module; providers read signatures only |
| symbol table indexes and scopes (`exact_symbols`, `module_callables`, `root_scope_symbols`, `qualified_types`, scopes) | 8.2 % | ~3650 rows | HIR lowering; `relocate_provider_*` in MIR |
| `symbols.symbols` rows without a defining module (locals, parameters) | 7.2 % | 370 rows | MIR lowering of this module |
| `enums` (own and materialized imported enums) | 4.6 % | 16 enums | MIR lowering |
| `symbols.symbols` rows of the module's own declarations | 0.8 % | 19 rows | everything |
| classes, structs, traits, impls, constants, the rest | 0.3 % | | |

Reading: the module's own code is about a quarter of its HIR (functions,
locals, own rows, own enums). **About 70 % is a per-importer replica of
declarations that other modules own**, rebuilt and retained once per importer.
That is why residency scales with (modules x imported surface) and why
dropping function bodies (`SIMPLE_MIR_SHARD_INTERFACE_HIR=1`) measured only
5-11 % per worker.

Growth over one week: the same row of run opus-15 (2026-11-07, source before
`6bf24744e00`, 2688 entries) averages **401 KB per module**; run 32 averages
766 KB (+91 %). `imported_layouts` (added 2026-11-12) is 230 KB of that
increase; the other ~135 KB per module is not attributed here.

Not measured: bytes per category in the native heap. Per encoded field the
run-32 cold figure is 5.9 MB / ~150 K fields = ~39 bytes; the tracked heap
counter covers object headers only (`rt_heap_live_bytes`, Rust runtime), so
the split between payload, allocator overhead and free-but-resident pages is
open (item 2 of the 2026-11-06 record).

## 3. Step 1 (landed in source): identity-only `imported_layouts` rows

`register_imported_symbol` filled `HirModule.imported_layouts` with a full
`HirStruct` per imported struct: one `HirField` per declared field with its
projected type, a `NilLit` default expression, flags and span. Readers in
`src/`: the codec, and `hir_frontend_type_unresolved`
(`35.semantics/lint/hir_frontend_diagnostics.spl`), which asks
`imported_layouts.contains_key(sym)`. Nothing in 50.mir, 60, 70 or 80 names the
field.

Change: `hir_imported_struct_row_v1`
(`20.hir/hir_lowering/imported_layout_row_v1.spl`) builds the row with the
importer SymbolId, the declaring name, visibility, span and generic flag and
`fields: []`. The key set is unchanged, so every lint verdict is unchanged; the
layout stays with its owner (the declaring module's `structs`, which is where
MIR already reads layouts from, through `providers`).

Seed evidence (`test/01_unit/compiler/20.hir/hir_imported_layout_row_spec.spl`):
a row encoded to 65 codec fields for a 1-field struct and 1352 for a 40-field
struct before, 32 and 32 after; the consumer's MIR text is identical with
field-carrying rows, identity rows and no rows.

Expected effect (**estimate**): rows go from ~290 to 32 encoded fields, i.e.
30.0 % -> 3.3 % of the HIR, a 27 % cut of encoded HIR (766 -> ~560 KB per
module, cache on disk 2353 -> ~1720 MB).
- Cache-hit residency (every MIR shard worker, every warm build): 27 % of the
  decoded HIR. No cache-hit RSS exists for this source; with the run-32 cold
  5.9 MB per module as a stand-in that is ~1.6 MB per module, ~4.9 GiB at
  3145 modules.
- Cold residency (the run-32 single-process row): lower, because a cold row
  shares spans and reuses the projected field types' sub-objects; per field it
  retains a `HirField`, a default `HirExpr`, a `HirType` and the projected
  type tree. Estimated 0.4-0.6 MB per module, 1.3-1.9 GiB at 3145 modules.
This is one step: it does not by itself put the full CLI build under 24 GiB
once MIR and codegen are added.

Contract note: the 2026-11-12 record described the side table as carrying the
layout for downstream consumers, and two spec examples asserted the field
payload. No such consumer exists; those two examples now assert the nominal
row (symbol id, name, not in `structs`). A consumer that needs fields should
read the declaring module, not N copies.

## 4. Step 2 (design): stop replicating imported symbol rows

33 % of the HIR is `HirSymbol` rows for imported declarations, 71 % of them
callables whose `type_` is a full function type built per importer. Options,
in order of containment:

1. **Demand registration.** A glob or facade import registers every exported
   callable and every method of every imported class. Register a row when the
   body first resolves the name (the surface already answers "does this name
   exist"). Risk: SymbolId allocation order changes, so MIR ids change;
   needs an A/B object comparison, not byte identity.
2. **Shared declaration table per declaring module.** Rows of module B's
   exports live once (session-owned); importers hold `(module, local id)`
   references. This is the same shape as `providers` in MIR and removes the
   replica for both HIR and the cache. It changes `SymbolTable` and the codec
   (a generator run).
3. **Interface-only residency extended to symbol tables.** For a module a
   process will not lower, keep only its own rows (0.8 %) plus what
   `providers` reads; today the projection keeps the whole table. Needs the
   reader inventory of `provider.symbols` in 50.mir to be closed first.

## 5. Step 3 (design): decode without un-sharing

`hir_module_decode` builds a fresh `Span`, `HirType` and default expression
for every occurrence. Interning the three most repeated shapes at decode
(spans by value, `Unit`/`Int`/`Str` types, the placeholder default) would cut
cache-hit residency without touching the format. Contained to
`20.hir/hir_codec*.spl`; needs a native measurement to size.

## 6. Step 4 (redesign, not started): bounded residency

Even with steps 1-3 a process that lowers N modules holds N modules of HIR,
because nothing can be freed (`build_session_memory_model_v1.md`: promoted
graphs are released only at session end). Two routes exist on paper:

- per-module release: make a lowered module's HIR an rc root
  (`rt_rc_share`) and release it after its MIR is emitted, keeping only the
  declaration summary for later consumers. Requires I5 (acyclic) for the
  module graph and the provider reads to go through summaries.
- process-level: per-file units (`native_file_worker_v1.spl`) with the
  module-scoped HIR load closure already restricted by
  `worker_hir_load_allowed_v1`; residency is then one module plus its import
  closure's declarations, and process exit is the release.

## 7. Other findings (not changed)

- **HIR shard worker, retained route (Stage 3):** a claimed module is
  re-parsed with `parse_full_frontend_stage4_streaming` (its own scope, result
  promoted), lowered by `lower_retained_surface_module` (HIR promoted) and
  stored in `phase_hir_modules` (`driver_hir_pipeline_lowering.spl` ~2174-2366);
  the worker then exits at ~2580 without reading that dictionary. The
  streaming route's shard transaction (`:755`) promotes no module. This is why
  a retained-route worker grows with what it lowers (run 32: ~12 GiB at ~415
  modules each). From code reading; not reproduced natively.
- **HIR worker price:** `SHARD_HIR_WORKER_KB_V1 = 9000000`
  (`src/app/cli/shard_mem_clamp.spl:351`), flat in module count, then scaled to
  the live admission budget by `file_worker_pool_hir_budget_kb_v1`
  (`file_worker_pool_refusal.spl:153`; run 32 printed `estimate=7025459 kB`).
  The MIR price is closure-scaled (`SHARD_MIR_WORKER_PER_MODULE_KB_V1`); the HIR
  price is not, although a retained-route worker grows per claimed module.
- **Coordinator:** 2.5 GiB at HIR pool admission (`[hir-shard] admission ...
  coordinator peak 2511172 kB`), 5.5-5.7 GiB flat during the MIR pool. The
  step between the two was not traced to a line. `rt_session_heap_end` trims
  with `malloc_trim`, but session end is opt-in (`SIMPLE_BUILD_SESSION_END=1`).
- **Knobs that are off by default and not set by any bootstrap script:**
  `SIMPLE_MIR_RETRACT_PROVIDER_TYPES` (`287a0d1cb16`),
  `SIMPLE_MIR_SHARD_INTERFACE_HIR`, `SIMPLE_BUILD_SESSION_END`. The full CLI row
  uses none of them.
