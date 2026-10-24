# Native-build: every MIR worker starts at 33-40 GB (frontend + mono garbage never freed) (2026-10-24)

Bug id: `native_build_per_worker_baseline_rss_2026_10_24`
Related: `mir_phase_rss_retention_2026_10_24.md`, `borrow_check_unscoped_rss_growth_2026_10_24.md`,
`stage2_native_build_rss_superlinear_threads_2026-10-23.md` (promote-then-reassign sites).

## Symptom
Self-hosted native-build of the 1471-module compiler closure: each MIR shard worker re-runs
parse -> HIR -> typecheck -> mono (`native_mir_shard.spl` header) and sits at ~16 GB at mono start,
~33 GB after mono, 36-40 GB before it lowers its first claimed module. Only 2 workers fit in 100 GB.

## Root model
The native runtime has no GC and no refcount (`src/runtime/runtime_native.c:8302`, `:8690`). Dropping a
reference frees nothing; only a transient scope (`transient_scope_begin/pause/promote/end`) or process exit
returns memory. So the baseline is the TOTAL allocation volume of every unscoped phase, not the live set.
Clearing `ctx.validation_module_blobs`, `ctx.modules` etc. after use would NOT lower RSS.

## Measurement (producer p2shard-9 Stage 2 `07c652da...`, compile worker pid, 1 s /proc VmRSS)
Launchers: scratchpad `basemem/run.sh` (cold), `run3.sh` (HIR-cache hit, `SCOPE=`), analyzer `an.sh`.
Entries: `src/app/zz_mirmem_probe/pa.spl` (204 modules), `pb4.spl` (472 modules; mono + hir_lowering +
MirLowering + borrow imports). RSS in MB at the end of each phase:

| phase end | 204 cold | 204 HIR-hit | 472 cold | 472 hit + discovery |
|---|---|---|---|---|
| load_sources | 509 | 383 | ~900 | - |
| parse | 835 | 798 | 1769 | 1769 |
| HIR lowering loop | 1383 | 1373 | 3354 | 3512 |
| validate | 1454 | 1515 | 3830 | 4067 |
| enum_contract | 1592 | 1515 | 4440 | 4067 |
| cold_receipts (= mono start) | 1986 | 1986 | 4934-5127 | 5171 |
| mono + MIR setup plateau | 3151 (A/A: 3151) | 3151 | 10507 | 8701 |

Growth law: pre-mono is ~linear at 9.7-10.9 MB/module (204/472/1471 = 9.7/10.5/10.9). The mono + MIR-setup
step is superlinear up to ~470 modules: 5.7 MB/module at 204, 11.8 at 472, ~11.6 at 1471 (33 GB - 16 GB).
Per-phase at 472: parse 1.9, HIR loop 3.4, validate 1.0, enum contract 1.3, cold receipts 1.5 MB/module.

## Culprits
1. **Mono full root walk** — `40.mono/monomorphize_integration.spl:500-526` (`process_modules` step 2) rebuilds
   EVERY non-template function body (`roots_rewritten=4179/4179` at 204, `9187/9187` at 472) through
   `rewrite_function` (:1043). The old bodies and the rebuild garbage are never freed. The existing,
   spec-pinned root discovery (`SIMPLE_MONO_ROOT_DISCOVERY=1`, `mono_root_is_relevant_v1`) rewrites only
   2 / 53 roots. Measured with the CURRENT producer: plateau 3151 -> 2807 MB at 204 (-344 MB, -1.7 MB/module),
   10507 -> 8701 MB at 472 (-1.8 GB, -3.8 MB/module); mono roots_ms 12767 -> 2654. Go-to-end verdicts
   identical (same failing modules, same diagnostics); `.o` files are not byte-deterministic even A/A
   (`__simple_str_const_N` numbering), so byte equality is not a usable oracle here.
2. **Cold-HIR receipt ABI encode unscoped** — `80.driver/cache/cold_hir_semantic_seed_v1.spl:125` (was :106)
   `hir_codec_abi_interface_encoded_v1(module)` runs on the driver loop with no scope; its canonical-part
   working set stays immortal. +470 MB at 204 (2.3 MB/module, reproduced 3x), +0.7 GB at 472.
   Only the finished `abi_payload` is consumed later (SMF export, package drafts), so it is promoted.
3. Not fixed (named): HIR lowering loop garbage (3.4 MB/module, of which the cached HIR blob is 0.3 MB),
   validation transports (`ctx.validation_module_blobs`, ~0.2 MB/module, `driver_hir_pipeline_lowering.spl:2240`),
   enum-contract/validate passes (2.3 MB/module), mono collect + constant-initializer rewrite (still
   rewrites every module's const initializers under discovery, :541), and MIR setup (+2 GB at 472).
   `validation_module_array` is a handle alias (RuntimeValue is Copy), not a second HIR copy.

## Fix
- `mono_root_discovery_env_v1` now defaults ON; `SIMPLE_MONO_ROOT_DISCOVERY=0` restores the full walk.
  Usable today without a rebuild: export `SIMPLE_MONO_ROOT_DISCOVERY=1` for the coordinator (workers inherit).
  Spec `test/01_unit/compiler/mono/mono_root_discovery_determinism_spec.spl` now pins `=0` for its full-walk
  baseline (it would otherwise compare discovery with itself) and gains a default-on case. UNEXECUTED: no
  full-CLI `bin/simple` exists on this host.
- `_cold_hir_abi_interface_encoded_scoped_v1` wraps the encode in begin/pause/promote/end, falling back to the
  unscoped encode when a scope is live (same discipline as `hir_module_encode_retained_v1`). Takes effect only
  after a Stage 2 rebuild; saving is an ESTIMATE (upper bound = the measured cold_receipts delta).

## Expected per-worker baseline at 1471 modules
33 GB post-mono minus >= 5.6 GB (discovery, 3.8 MB/module) minus <= 2.2 GB (receipts) ~= 25 GB; ~29 GB
before first MIR module instead of 36-40 GB. Still not "a few GB": the remaining ~10 MB/module pre-mono is
unscoped frontend garbage (item 3); bounding it needs per-module scopes in HIR lowering/validation.
