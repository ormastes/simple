# Stage 2 (Windows) frontend/HIR wall time: where it goes — 2026-10-16

Status: OPEN (two partial fixes landed with this record; main costs remain)
Binary: `stage2-admitted/simple.exe` sha256 `14e1e40e9769…ffe59` (release_phase3 lane, Windows 11, 24 cores)

## Measured

Source: `verification.run2/logs/{compiler_cli_build,test_runner_build}.log` plus a
profiled re-run of the test-runner closure (`--entry src/app/test_runner_new/main.spl`,
267 physical / 512 logical modules) with `SIMPLE_COMPILER_PHASE_PROFILE=1`
in a scratch storage root (same policy env: `SIMPLE_PARSE_SHARD_MAX=1` etc.).

| step | test runner (267 mod) | CLI (2686 mod) |
|---|---|---|
| parse phase (`phase=parse ... complete`) | 40-64 s | **1,293,728 ms** |
| of which per-file parse work | 37 s | no timestamps (lead c unmeasurable: `phase2:surface:file:*` carry none) |
| surface_build / surface_freeze (non-streaming) | 16.4 s / 5.8 s | — |
| HIR loop, cold (shard child) | 83 s (~310 ms/module) | 521 s for first 1047 modules, then killed |
| HIR loop, 100 % cache hits (real worker) | 43.6 s (~160 ms/module) | — |
| **cold HIR receipts** (`capture_cold_hir_typed_receipts_v1`) | **89.1 s** | not reached |
| MIR lowering | ~1.35 s/module floor, even `functions=0` | not reached |

* The "180 s post-HIR step with `hits=267`" is `phase3:hir:cold_receipts` (89 s in the
  re-run, `+86312ms -> +175366ms`; 98 s in run2). It has no internal receipts.
  With a 1-module closure (`src/app/classrepro/main.spl`) the same step takes
  **6.4 s** — a fixed cost from admitting the whole 14,443-row SCV inventory
  (`cold_hir_source_inventory_admit_v1`: inventory digest, snapshot SHA, two dicts).
  The rest (~310 ms/module, ~160 ms per logical row) is per-row: a full typed-ABI
  re-encode (`hir_abi_interface_encoded_v1`) plus row admission.
* HIR per-module cost in the CLI build grows with position, not import count
  (lib modules with ≤5 `use` lines, ms per source line by position bucket of 350):
  1.16 → 1.94 → 2.74 → 9.61. Accumulated-state cost, i.e. O(n²) overall.
* MIR: 1-module closure lowers its module in 67 ms; in the 267-module closure every
  module costs ≥1.3 s (`lib.io_runtime functions=0` 1448 ms). Per-module work scales
  with closure size — for 2686 modules that floor alone is ~1 h. Separate bug.
* Shard clamp (lead a): `[shard] threads=1 (requested 4 ... worker budget=3000000 kB)`
  — 3 GiB lane share ÷ 3 GiB HIR worker budget = 1. `product-frontend-policy.shs:26-28`
  hard-rejects any `SIMPLE_PARSE_SHARD_MAX` other than 1 on every host (deliberate,
  OOM history in `native_build_main.spl:615-624`). Observed RSS ~0.9-3.3 GB per
  process, so raising it is an owner policy decision, not done here.

## Fixed in this change (complexity fixes; wall-time delta NOT measured — the
admitted exe cannot be rebuilt in this session)

1. `driver_log_typed_hir_abi_interface_v1` and the HIR shard transaction
   (`driver_hir_pipeline_lowering.spl`) computed a full ABI encode + SHA-256 per
   module only for an `[abi-interface]` `log_phase` line that is dropped unless
   phase tracing is on. Now gated on `driver_phase_trace_enabled()`. Removes one
   ABI encode per module from every HIR path (hit path, cold path, shard).
2. `canon_seq` (`00.common/cache/canonical_identity.spl`) used
   `body = body + item`; `rt_string_concat` mallocs and copies the full
   accumulator every time (`runtime_native.c:3786`, `collections.rs:2817`), so
   large sequences were O(n²) bytes. Now `encoded_items.join("")` (linear,
   `rt_string_join`), byte-identical output so digests/cache keys are unchanged.

## Inferred, not verified (no symbols / no PDB; cdb sampling not usable)

* Per-file/per-module `rt_transient_heap_promote` of long-lived registries
  (`driver_promote_retained_frontend_owners_v1`, `promote_symbol_table_transient_owners`,
  `promote_phase_memo_transient_owners`, `driver_promote_frontend_registry_owners`;
  ~7 calls per module in `lower_streaming_surface_source`, 3 per file in
  `add_streaming_module_surface`) walks the whole reachable graph each time:
  `runtime_native.c:2795-2826` classifies persistent arrays/dicts/enums as nodes
  and traverses them; the Rust runtime (`collections.rs:2274-2297`) does the same.
  Cost grows with everything retained so far — matches the position-driven HIR
  curve. Pruning persistent containers is UNSAFE today: there is no write barrier,
  so a persistent registry can hold transient children. Fix shape: dirty bit set on
  array/dict store into a persistent container, walk only dirty containers.
* Cold-receipt per-row cost beyond the ABI encode: candidate is passing the
  14,443-entry `CompileSourceInventoryV1` and admission dicts by value into
  `cold_hir_source_inventory_row_v1` for each of 512 rows.

## Same pattern elsewhere (not changed)

String accumulation `x = x + ...` in loops over unbounded rows:
`80.driver/cache/catalog/cache_catalog_projection.spl:93` (catalog digest over all
rows), `00.common/cache/darwin_runtime_provider_manifest.spl:154,190`,
`80.driver/cache/cas/verified_cas_kind_registry_v1.spl:107`,
`80.driver/cache/cold_package_scc_v1.spl:34`. Not on the measured hot path.

## Follow-up 2026-10-16: promote re-walk CONFIRMED (mechanism + micro-benchmark); no safe runtime fix yet

### Mechanism (read from source, `origin/release_phase3` @ `a89ae76afd0`)

* `rt_core_transient_classify` (`src/runtime/runtime_native.c:2700-2754`) returns
  "tracked node" for every *registered* ARRAY/DICT/ENUM/FLOAT/INT/UINT/CLOSURE
  without reading `transient_scope_id`; only STRING (2742-2748) checks ownership.
  Under `SIMPLE_RUNTIME_MEMORY_OWNER` (the capsule lane) persistent structs are
  nodes too: `rt_transient_raw_words` (`runtime_memory.c:171-198`) falls back to
  `rt_struct_alloc_lookup_size` for structs allocated before the scope.
* So `rt_transient_heap_promote` (2767-2859) traverses the *entire* reachable
  graph — persistent part included — every call; the mark loop (2852,
  `if (*object_scope == scope_id)`) is a no-op on everything already persistent.
  Per child word: raw-owner hash probe (+ struct-registry probe), immortal-registry
  probe, then insert into a per-call `calloc`'d seen set that rehashes on every
  doubling.
* Rust runtime (`src/compiler_rust/runtime/src/value/collections.rs:2254-2298`,
  `transient_heap_children` 2172-2215) is the same shape: no scope filter, full walk.
* Hard cliff, not only slowness: `RT_CORE_TRANSIENT_MAX_NODES = 1<<22`
  (`runtime_native.c:2651`). Once one root's reachable graph (persistent part
  included) exceeds ~4.2M nodes, `rt_core_transient_plan_push` returns 0 and the
  promote FAILS ("... ownership promotion failed for <module>").

### Which call sites are the O(n) term (per module)

* HIR: `lower_streaming_surface_source` / retained lowering
  (`80.driver/driver_hir_pipeline_lowering.spl:483-582`):
  `promote_phase_memo_transient_owners` (`20.hir/hir_lowering/types.spl:908`,
  already batched into one seen set, but the memos accumulate across ALL modules),
  then `driver_promote_retained_frontend_owners_v1`
  (`driver_source_pipeline_parsing.spl:298`: 4 registries + parser slots +
  declaration metadata + resource registry + parse cache + shared-parse rows +
  coverage inventory — all cross-module). Symbol-table containers
  (`types.spl:882`) are module-local and are NOT the growing term.
* MIR (same pattern, explains the ~1.35 s/module floor that scales with closure
  size): `lower_module_transient_scoped` (`50.mir/_MirLowering/module_lowering.spl:1737-1745`)
  promotes the module, then `promote_transient_owner`
  (`_MirLowering/transient_owner.spl:13+`, ~30 SEPARATE walks, one per lowering
  field incl. `symbols`, `fn_return_types`, `callable_link_names`), then
  `bootstrap_mir_registries_promote` (`bootstrap_globals.spl:116-155`, 20
  cross-module arrays) and `bootstrap_fn_registries_promote`
  (`mir_data.spl:1270`, 17 cross-module dicts). Every one re-walks everything
  accumulated by earlier modules.

### Micro-benchmark (C runtime, `-DSIMPLE_RUNTIME_MEMORY_OWNER=1`, clang 18, Windows 11)

Persistent registry array created before the first scope; per "module": begin
scope, append 50 entries (`[ [1,2], 3 ]`) plus 200 garbage entries, pause,
time one `rt_transient_heap_promote`, end. 2000 modules:

| modules | registry size | promote(registry) | promote(only new entries) |
|---|---|---|---|
| 1..400 | ≤20k | 1.69 ms/module | 0.009 ms |
| 401..800 | ≤40k | 5.27 ms | 0.009 ms |
| 801..1200 | ≤60k | 13.7 ms | 0.008 ms |
| 1201..1600 | ≤80k | 21.1 ms | 0.006 ms |
| 1601..2000 | ≤100k | 34.1 ms | 0.005 ms |
| total | | **30,334 ms** | **14.7 ms** |

Quadratic in total (and per-call cost is itself slightly superlinear in graph
size: ~0.17 → ~0.38 µs per entry, seen-set growth / cache misses). The
"only new entries" column is a COST PROBE ONLY — it is not a correct promote:
it skips the registry's own backing store, which `rt_array_push` may have
reallocated inside the scope (see the `bootstrap_globals.spl` docstring).

### Why no fix landed with this follow-up

Pruning the walk at already-persistent containers needs a complete write
barrier, and one cannot be added in the runtime alone:

* Struct field stores are INLINE in native codegen: Cranelift `SetField`
  (`70.backend/backend/cranelift_codegen_adapter.spl:715-721`) emits a raw
  `cranelift_store` — no runtime call to hook. A persistent struct reachable only
  through a persistent array can receive a transient value with no runtime
  visibility; pruning that array would free a live object (UAF).
* Array/dict element stores DO go through runtime calls (`rt_array_set`,
  `rt_array_push`, `rt_dict_set`, …), so a dirty bit there is possible but not
  sufficient on its own.

Fix options, in order of safety:
1. Codegen-emitted barrier: `SetField` on a base whose `transient_scope_id == 0`
   (or a per-object "persistent" bit) records the base in a per-scope remembered
   set; runtime mutators (`rt_array_set/push/insert/extend`, `rt_dict_set/remove`,
   `rt_closure_set_capture`, enum payload writes) do the same. Promote then walks
   transient nodes + remembered persistent nodes only. Must land in C runtime,
   Rust runtime, and every backend (Cranelift, LLVM, native isel) together, and
   be proven by a selfcheck that writes a transient value into a persistent
   struct reached only via a persistent array.
2. Call-site incremental promotion for append-only registries of immutable leaves
   (text/int arrays in `bootstrap_globals.spl`, `mir_data.spl`): promote the new
   tail plus the container's backing store via a new shallow runtime entry point.
   Needs per-registry proof that no existing slot is overwritten in place.
3. Constant-factor only (does not change the curve): batch the ~30 separate
   MIR-owner walks into one seen set like `promote_phase_memo_transient_owners`.

Unverified: the Stage 2 exe's exact runtime lane (capsule C runtime with
`SIMPLE_RUNTIME_MEMORY_OWNER` assumed); the share of the real 1294 s parse /
HIR curve attributable to promote (needs a profiled rebuild with a promote
timer, not possible from the read-only admitted exe).
