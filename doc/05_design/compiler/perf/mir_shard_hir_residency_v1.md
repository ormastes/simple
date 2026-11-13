# MIR shard worker HIR residency: bodies only for claimed modules

Status: **helper + specs landed, pipeline wiring opt-in and default OFF**
(`SIMPLE_MIR_SHARD_INTERFACE_HIR=1`). No RSS claim is made here; the
measurement command is at the end and needs a native Stage 3 run.

Related: `doc/05_design/compiler/incremental_build/mir_shard_export_summaries.md`
(stage 1 landed, stage 2 "summary-only lowering" designed but not wired — this
document is the narrower step that reuses the `HirModule` shape instead of the
declaration carrier), `doc/05_design/compiler/perf/mir_fork_workers_cow_v1.md`
(copy-on-write children, experimental, orthogonal), #8504 layer 1 (PR #8746,
MIR ownership scoped to the unit's held HIR — the per-file unit route, which
this document does not touch).

## Problem (measured by the coordinator, 2026-11-13)

Phase 3 (Stage 3 compiler build, two-pass route `SIMPLE_FILE_WORKERS=0`, go-to-end
MIR shard pool, PR #8744) is memory bound: each MIR shard worker holds the full
HIR of the program (~19–25 GiB RSS), so two concurrent MIR workers need
50–60 GiB and the shared 121 GiB host usually fits one — the pool is
effectively serial.

## Current mechanism (file:line, at `05c30927768`)

1. **Worker spawn.** `src/app/cli/native_build_main.spl:1456` `run_mir_shards`
   spawns `count` ordinary workers (`run src/app/cli/native_build_worker.spl`,
   `SIMPLE_MIR_SHARD=<i>/<n>`, `SIMPLE_MIR_SHARD_QUEUE`, `SIMPLE_MIR_SHARD_OWNER`).
   Each worker runs the whole front half again
   (`src/compiler/80.driver/driver_build/native_mir_shard.spl:1-23`).
2. **HIR load = full decode + promote.** The HIR stage loop
   (`src/compiler/80.driver/driver_hir_pipeline_lowering.spl:1302-1306`) calls
   `hir_cache_load_parsed_v1` for every module after the per-module gate
   `worker_hir_load_allowed_v1` (only a module-scoped per-file child restricts
   it; a MIR shard worker never does). `hir_cache_load`
   (`src/compiler/80.driver/driver_hir_cache.spl:421-462`) decodes the blob in a
   transient scope, then **deep-promotes the whole module to the persistent
   heap**. There is no collector: a promoted module is immortal
   (`driver_types.spl:1436` `evict_hir` drops the dict entry, not the memory).
   Consequence: *dropping bodies after registration frees nothing*; the only
   residency lever is to promote less.
3. **Feed.** `src/compiler/80.driver/driver_pipeline_lowering.spl:736-738` builds
   `ctx.mir_feed_modules` = every `ctx.hir_modules` entry and passes it as
   `providers` to every `lower_module` call.
4. **Claims happen after HIR.** The worker publishes the ledger inventory and
   claims modules one at a time in LPT order inside `lower_to_mir`
   (`driver_pipeline_lowering.spl:1405-1438`, claim at `:1549`
   `native_mir_shard_claim_v1`, cap `ceil(schedule/count)`), so ownership is
   **not known at HIR-load time**. Claims are a ledger race; a crashed worker's
   held claims are sealed and replaced (`hir_shard_recovery_*`).
5. **Lowering.** `:1578` reads `ctx.hir_modules[source_lookup_name]` and
   `:1613` lowers it with `lower_module_transient_scoped(hir, ctx.mir_feed_modules, …)`.

## What MIR lowering of a claimed module reads from OTHER modules

Verified on this tree (the export-summaries doc's 24-row inventory is the
reference; rows that read bodies were re-checked):

- `providers` reads are declaration-only: `symbols`, `constants` (values),
  `functions` (signature: params incl. `HirParam.default`, `return_type`,
  `effects`, `is_extern`), `traits` (`methods`, **`defaults` bodies** —
  remapped into consumers by `declaration_default_rewrite_v1.spl:354,516`),
  `structs`, `classes` (methods are `SymbolId`s into `functions`), `enums`,
  `impls`, `needs_initialization`
  (`50.mir/_MirLowering/{provider_globals,provider_metadata,declaration_*,exact_extern_provenance}.spl`).
- The body prescan `prescan_block_for_struct_types`
  (`module_lowering.spl:4218`) walks **the module being lowered only**
  (`lower_module` `:3656`, and the flat bootstrap twin
  `bootstrap_globals.spl:546` over `module_index`'s own rows). It is not a
  cross-module body read. Its facts accumulate across modules on one
  `MirLowering` instance, but a shard worker never lowers an unclaimed module
  today either, so an unclaimed module's bodies are already absent from that
  state.
- The driver's own setup and post-HIR passes read no bodies:
  `driver_pipeline_lowering.spl` / `driver_hir_pipeline_lowering.spl` /
  `driver_mir_physical_owners.spl` / `driver_aot_pipeline.spl` contain no
  `.body` read; `value_struct_layout_declarations_v1` takes structs + symbols;
  `driver_admit_nogc_param_effects_v1` reads module flags;
  `analyze_collections_before_mir` reads registries; `guard_api_publication_v1`
  reads no bodies. Monomorphization was deleted (`200a05f5bc8`), so no generic
  template bodies are instantiated across modules.
- **Lane caveat (not a cross-module read, but a residency leak):** under
  `SIMPLE_BOOTSTRAP=1` without `SIMPLE_BOOTSTRAP_STAGE4=1`
  (`bootstrap_hir_modules_add_from_module`, `20.hir/hir_lowering/_Items/lowering_helpers.spl:81`)
  every cache-hit module's function rows are also adopted into the
  `BootstrapHirStore` session. Rows adopted from an interface-only module are
  interface-only too, so the win carries over; the flat prescan reads only the
  rows of the module it lowers.
- Whole-program bootstrap lowering (`driver_pipeline_lowering.spl:1053-1168`,
  `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`) lowers the entire closure in one process
  and is not a shard lane; the predicate below does not arm there because no
  `SIMPLE_MIR_SHARD` is set.

## Design: interface-only load, reload on claim

Narrowest change that keeps the ledger protocol, the feed shape and the
lowering code untouched:

1. **Arm once per process** (`mir_shard_hir_residency_refusal_v1`,
   `src/compiler/80.driver/driver_mir_shard_hir_residency_v1.spl`): arms only
   when `SIMPLE_MIR_SHARD_INTERFACE_HIR=1` AND `SIMPLE_MIR_SHARD` is set AND
   none of: link child (`SIMPLE_MIR_SHARD_LINK`), export writer
   (`SIMPLE_MIR_SHARD_EXPORT_WRITE`), fork root (`SIMPLE_MIR_FORK_WORKERS>1`),
   per-file unit child (`SIMPLE_FILE_WORKER_HIR_QUEUE`), module-scoped child
   (`worker_hir_loads_restricted_v1()`). Every refusal is named and printed
   once. Set-once, like `worker_hir_restrict_loads_v1`.
2. **Project before promote.** `hir_cache_load_parsed_v1(..., interface_only)`
   threads one flag down to `hir_cache_load_in_owned_scope`, which — still
   inside the transient decode scope — returns
   `hir_module_interface_only_v1(decoded)`: every function body replaced by the
   codec's placeholder block except extern, generic (`type_params > 0`) and
   `const fn` functions; everything else (symbols, signatures, parameter
   defaults, constants, structs/classes/enums/bitfields, traits incl. default
   bodies, impls, AOP advices, nogc rows, layouts) is kept by value. The scope
   end frees the full decode; only the projection is promoted. The HIR stage
   passes `interface_only = armed and not is_requested_bootstrap_entry` and
   records `(path -> module, cache key, parser binding, library mode, kind)`.
3. **Reload on claim.** In the claim loop, right after
   `shard_claimed_names.push(name_direct)` (`driver_pipeline_lowering.spl:1575`),
   an interface-only module is reloaded from the cache with the recorded key
   (`interface_only = false`), the `ctx.hir_modules` entry is replaced, and the
   module is marked `full`. A refused reload removes the entry so the existing
   ICE boundary records "MIR lowering missing HIR module" for that one module
   (fail closed, go-to-end continues). The feed keeps the interface copy of the
   module: providers are declaration-only (above).
4. **Held set invariant** (spec): after the loop a worker holds full bodies for
   exactly `{entry} ∪ claimed` and interface-only HIR for every other module.

Expected residency: bodies for `≈ 1/K` of the modules + declarations for all,
instead of bodies for all. Each claimed module costs one extra cache decode.

## Why not the alternatives

- *Strip after registration*: frees nothing (promoted heap, no collector).
- *Claim before HIR / static partition*: changes the ledger protocol and the
  crash-replacement granularity (a dead worker would seal `cap` claims, not one).
- *Stage 2 summary-only lowering*: right end state, but needs the declaration
  repository route, rebuilt process-global registries and order-independent
  counters first (its own doc lists them).
- *Fork CoW children*: already exists as an experiment; orthogonal.

## Risks

- A provider body read that the inventory missed would lower against an empty
  body with no diagnostic. Mitigation: default OFF; the value-semantics spec
  (consumer MIR text identical with a full vs interface-only provider); the
  Stage 3 qualification below must compare outputs, not only RSS.
- `hir_cache_load` counts the reload as a second hit (`[hir-cache] hits=`
  receipts rise by the claimed count).
- A cache entry evicted between load and claim (disk cache bound) fails that one
  module closed rather than silently.
- The identity/`SIMPLE_CACHE_SCOPE` exclusion list in
  `cache/native_build_environment_identity.spl:268` does not list the flag; a
  run with the flag set gets its own object scope, which is harmless for an A/B.

## Qualification + measurement (coordinator, run 21, quiet box)

Two Stage 3 runs that differ only in the flag, same source sha, pinned cache
scope, record binary identity first:

```bash
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"
# A (today):
SIMPLE_CACHE_SCOPE=run21-a SIMPLE_MIR_SHARD_INTERFACE_HIR=0 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh --resume-stage3-from-admitted=<admitted-out> \
  --backend=cranelift --output=build/bootstrap-run21-a 2>&1 | tee build/bootstrap-run21-a.log
# B (interface-only HIR in MIR shard workers):
SIMPLE_CACHE_SCOPE=run21-b SIMPLE_MIR_SHARD_INTERFACE_HIR=1 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh --resume-stage3-from-admitted=<admitted-out> \
  --backend=cranelift --output=build/bootstrap-run21-b 2>&1 | tee build/bootstrap-run21-b.log
# per-worker peak: the pool's own receipt (process_peak_rss_kb, native_build_main.spl:957)
grep -h "\[mir-shard\]" build/bootstrap-run21-{a,b}.log | grep -i "peak\|rss\|hir-residency"
# value check: MIR shard PASS sidecars / object inventory must match
diff <(grep -h "PASS" build/bootstrap-run21-a/*/mir-queue*/* | sort) \
     <(grep -h "PASS" build/bootstrap-run21-b/*/mir-queue*/* | sort)
```

Read `[mir-shard] hir-residency armed|refused reason=…` in B's worker logs
first: a refusal means nothing was measured. Only after B's objects match A's
should the flag be considered for a default.

## Integration point for a shared read-only HIR (node-store lane)

This change decides **which** modules a worker holds and in what form; it does
not touch node representation. A frozen, position-independent module HIR
(mmap of a serialized arena, or a fork copy-on-write page set) plugs in at
exactly two places:

1. `hir_cache_load_in_owned_scope` (`driver_hir_cache.spl`): today "decode +
   promote". A shared arena replaces the promote for the interface-only
   projection *and* for the full module — the projection becomes a view
   (declarations only) over the shared module instead of a copy.
2. The claim-loop reload (`driver_pipeline_lowering.spl`, after
   `shard_claimed_names.push`): today "decode the cache entry again". With a
   shared frozen module it is "attach the body view"; `mir_shard_hir_residency_*`
   keeps recording which modules are body-resident so the held-set spec still
   holds.

## Fork copy-on-write (SIMPLE_MIR_FORK_WORKERS) findings

`driver_build/native_mir_fork_v1.spl` already forks N children at the claim
loop from ONE root that ran the whole front half; children inherit HIR
copy-on-write. It is experimental, opt-in, and `run_mir_shards` collapses the
pool to one root when set. Two open bug records explain why it is not the
default: `doc/08_tracking/bug/mir_fork_child_heap_registry_cow_resize_2026-10-25.md`
and `mir_fork_wait_returns_before_children_2026-10-24.md`. CoW and interface-
only residency compose: a root with interface-only HIR shares a smaller page
set, and each child reloads only its claimed bodies privately. The arming
predicate currently refuses `SIMPLE_MIR_FORK_WORKERS>1` (named reason
`fork-workers`) so the two experiments are measured separately first.
