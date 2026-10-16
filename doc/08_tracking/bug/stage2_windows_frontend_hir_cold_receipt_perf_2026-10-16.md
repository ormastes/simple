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
