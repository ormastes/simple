# Stage 3 closure loop: RSS grows 20-36 MB per module with the provider feed (release_phase3)

- Status: fix-implemented-verification-pending
- Date: 2026-10-20
- Platform: aarch64-unknown-linux-gnu
- Severity: P1 (Stage 3 tree cap 52 GiB is nearly exhausted by the closure loop)

## Observation

Stage 3 resumed from bootstrap-r16b (release_phase3 f9527544c50 + the
rt_process_rss_kib capsule fix; Stage 2 sha256 645e62a815d0...), DIRECT
route (SIMPLE_NATIVE_BUILD_THREADS=1), closure 1352 modules. Closure-loop
lowering runs with the transient scope (#3919) and the provider feed (#3938):

- HIR complete: RSS 6.6 GB (heap_live 2.34 GB).
- after ~1123 closure modules (2 h): RSS 46.6 GB, i.e. ~36 MB/module on
  average; sampled rate at that point ~20 MB/module (+352 MB over 18
  modules).
- throughput 18.4 modules/min (r8 base without the provider-walk perf chain:
  4.7/min; heap +8.2 MB/module, RSS +28 MB/module).

Projected end of closure loop: ~51 GB against the 52 GiB tree cap, leaving
little room for entry lowering and codegen. The memory-snapshot file only
covers HIR, so heap vs RSS in MIR is not split here; the r8-base run's
`SIMPLE_MIR_SECTION_PROFILE_FILE` showed heap +8 MB/module vs RSS
+28 MB/module, i.e. most of the growth was not live heap.

## Next step

Run the closure loop with `SIMPLE_MIR_SECTION_PROFILE_FILE` (heap_live and
rss per `s4_promote_*` mark) on this tree to split retained heap from
allocator retention, then find which per-module provider registration
products survive the transient scope.

**Revalidated 2026-11-02: still plausible because the report title (Stage 3 closure loop RSS grows 20-36 MB per module with the provider feed (52 G) has no merged fix or passing regression cited in its tracking doc; no merged fix commit with a passing regression is cited in this doc.**

## Resolution (2026-11-02, p1boot-closure-rss) -- fix-implemented-verification-pending

Source triage on release/1.0.0 (ed65bf432d3). The retention described here was
fixed the same day the report was filed; the report row was never updated.

Root cause: with the provider feed, every consumer module re-ran
`register_provider_struct` / `register_provider_class` over the whole closure
(provider_metadata.spl:694,754). They relocate field types/defaults into the
consumer's SymbolTable (consumer-specific ids) and overwrite the cumulative
`struct_field_*` rows (promoted, immortal), orphaning the previous consumer's
copy: retained memory grew with modules x closure structs. Per-consumer
trait/global/extern tables were likewise promoted then replaced.

Landed fixes:
- 8ec58deca84 retire per-consumer tables and detach the provider feed in stage3
  closure scopes (module_lowering.spl:2431-2490).
- 76473a1f1d7 demand provider layouts for stage3 bootstrap-closure modules
  (module_lowering.spl:2831 `layout_demand`; skips eager pass at :2875/:2886).
- cc601e8f3d3 demand provider layout rows, session enum rows.
- Specs: test/01_unit/compiler/50.mir/provider_layout_demand_spec.spl,
  trait_scratch_scope_retirement_spec.spl, provider_method_scope_retirement_spec.spl,
  test/01_unit/compiler/driver/bootstrap_fixed_closure_scoped_lowering_spec.spl.

Not measured: no stage2/stage3 binary run on this host (6 GB cap); the
post-fix per-module RSS slope is UNVERIFIED.

Verification (needs a stage2 binary):
1. Resume the stage3 closure loop (bootstrap-fixed, direct route, SIMPLE_NATIVE_BUILD_THREADS=1).
2. Set SIMPLE_MIR_SECTION_PROFILE_FILE; compare rss/heap_live at `s5_scope_end`
   between module 100 and module 1000.
3. PASS: slope < ~2 MB/module, heap_live flat. Otherwise next suspect: enum
   registry rows via register_provider_enums_v1 (still eager per consumer,
   module_lowering.spl:2907).
