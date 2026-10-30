# Stage-3 HIR phase: 59 min single-process — measured breakdown and root causes

Date: 2026-10-25 · Area: `80.driver` HIR pipeline, native-build sharding, mono ·
Status: partially fixed (see table); remaining items filed below.

## Measured (frozen Windows stage2 `e9b561d1…c993`, release/1.0.0 sources)

Full `bootstrap_main` closure (1442-1453 modules), from `s3-bis-new/build.log`
and the phase-profile / mem-snapshot event files of attempt 780574:

| Segment | Time | Share |
|---|---|---|
| HIR loop, per module (avg 1.43-1.77 s) | 2566 s | 75 % |
| ‣ reparse + lower + promote (`hir-file-start→post-lowering`) | avg 756 ms | |
| ‣ `post-diagnostics→post-store` (HIR cache store incl. selfcheck when enabled) | avg 374 ms | |
| ‣ `post-store→next file-start` (validation blob encode, layout projection, progress I/O) | avg 292 ms | |
| Post-loop: nogc param-effect admission (O(n²)) | 198 s | |
| Post-loop: RT-criticality blob decode (85 % refused) | 78 s | |
| Post-loop: any_escape + enum_contract + cold receipts | 26 s | |
| Monomorphize (`collect_ms=43883 roots_ms=219560`, roots=23014 rewritten=7279) | 267-414 s | 10 % |

Per-module cost is flat across the closure (first 150 modules avg 2.2 s, rest
0.6-1.1 s): it is per-module repeated work, not O(done²).

308-module `lint_entry` closure, in-process (probe run4, `SIMPLE_HIR_PHASE_PROFILE=1`):
HIR lowering proper = 14.4 s / 308 = **47 ms per module** (functions 6.0 s for
4923 fns = 1.2 ms/fn; imports+glob ≈ 5 s for 24 777 registrations = 0.2 ms each;
declare 1.1 s; other 2.3 s). The driver segments around it cost more than the
lowering: reparse+promote ≈ 90 ms, `post-store→file-start` 105 ms per module.
So "HIR per module should be milliseconds" holds for the lowering; the phase
time is driver overhead, serialisation, and the 1453-wide import sets of the
compiler's own modules (0.2 ms × thousands of registrations).

## Root causes and state

| # | Cause | file:line | State |
|---|---|---|---|
| 1 | Cache scope `SIMPLE_FRONTEND_CACHE_SCOPE` never published → `[hir-cache] disabled reason=no-compiler-scope` → HIR shards refused, MIR shards `claims=0`, everything single-process | `driver_source_pipeline_parsing.spl:962` (enum gate), `native_build_main.spl:1186` (spawn before publish), `driver_hir_pipeline_lowering.spl:1087` (digest forced `""` under explicit policy) | PR in flight (WP-A). Reproduced: run3 default = disabled; run2 with the scope set by hand = 4 shards lowered 307/308 |
| 2 | O(n²) nogc param-effect admission with HirModule copies | `driver_hir_pipeline_support.spl:410-480` | fixed #4557 (+ `7db42fe70fa`) |
| 3 | Validation blob encoded per module, decoded again, 85 % refused | `driver_hir_pipeline_lowering.spl:2291`, `rt_criticality_validation.spl:731` | fixed #4562 (`SIMPLE_HIR_VALIDATION_BLOBS=1` restores) |
| 4 | Reparse of every module inside the HIR loop (`parse_full_frontend` / `_stage4_streaming`) because phase-2 parse output is not retained | `driver_hir_pipeline_lowering.spl:1931-1979, 631` | open; per-file pipeline makes it one parse per file (design `true_per_file_pipeline_v1.md`) |
| 5 | Frontend `.fpc` cache HIT costs 455 ms/file vs 130 ms cold parse (pure-Simple `sha256_text` over the blob + flat-pool replay) | `frontend_parse_cache.spl:139-182`, `frontend.spl:127-150`, `sha256.spl:217` | open — a hit must be cheaper than a parse before the cache is turned on by default |
| 6 | HIR cache hit decodes ~196 ms/module (codec) | `driver_hir_cache.spl:252-296` | open; 1453 hits ≈ 285 s serial in the parent — the per-file design removes the parent adoption pass |
| 7 | Global mono pass: 32 % of roots "relevant" (`discovery_method_names` = last-member names of generic methods/fields, so common names match everything) | `monomorphize_integration.spl:453-680, 3693-3900` | P4 module-scoped mono in flight; tighten relevance separately |
| 8 | Import re-registration per importer (0.2 ms × every imported name, glob imports register whole facades) | `module_import_registration.spl:102-400` | open; lazy on-lookup registration is the structural fix |
| 9 | `mem_snapshot_begin() < 0` → "SIMPLE_MEM_SNAPSHOT_FILE could not be established safely" when the retained loop finishes under a snapshot file (probe run4) | `driver_hir_pipeline_lowering.spl` retained loop post-loop | open, diagnostics only |

## Evidence files

Probe runs (scratchpad of this session; same env shape as the stage-3 lane):
run1 shards no scope → all workers "HIR cache identity unavailable"; run2 scope
set → `[frontend-cache] hits=308`, shards lowered 307/308, stores refused only by
the pre-#4504 selfcheck; run3/run4 in-process → `no-compiler-scope`; run4
`[hir-prof]` 308 rows summarised above. Stage-3 logs:
`C:/dev/wt-rel3-new/build/s3-bis-new/build.log`,
`.simple/storage/build/bootstrap/stage3/x86_64-pc-windows-gnu/{phase-profile,memory-snapshot-v1}.780574.events`.

## Expected after a stage2 rebuild with #4557 + #4562 + WP-A

Post-loop 425 s → ~30 s; per-module loop −292 ms (blob) and, with HIR shards
admitted (12 workers at the lane's 3 GB/worker budget), the lowering spreads
12-wide while the parent adopts cache hits (~0.2 s each) instead of lowering.
Rough: 59 min → 10-15 min for the HIR phase; the 1-minute target needs the
per-file pipeline (no parent adoption pass, one parse per file, module-scoped
mono) — `doc/05_design/compiler/incremental_build/true_per_file_pipeline_v1.md`.
