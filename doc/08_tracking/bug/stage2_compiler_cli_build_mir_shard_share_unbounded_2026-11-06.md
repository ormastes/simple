# Stage 2 `compiler_cli_build` hits the tree RSS cap during MIR (2026-11-06)

Status: mitigated (shard-count pin in `scripts/bootstrap/phase-c-backend-commands.shs`).
Root retention in the MIR shard worker remains open; see "Not fixed" below.

## Symptom

Bootstrap run 10 (base `a720cb10557`, `build/bootstrap-opus-10`) aborted in
Stage 2 compiler tests. Row `compiler_cli_build` reached the 52 GiB
whole-tree cap at MIR schedule position 1088 of 3031. The tree held two
`compiler.snapshot` processes of ~25 GiB each.

## Not a regression

Run 4 (base `13a060d644e`, 2026-11-05, before #7177 `xray_mode` and #7184 HIR
arity) shows the same per-worker curve:

| MIR position | run 4 RSS (MiB) | run 10 RSS (MiB) |
|---|---|---|
| 50  | 19274 | 19337 |
| 300 | 20955 | 21037 |
| 550 | 20746 | 21052 |
| 1100 | — | 25231 |

Earlier runs failed before MIR, so this cost was never reached.

## Mechanism

- The row runs `[mir-shard] shards=2 parallel=2`. The coordinator's default
  shard count is the concurrent worker count
  (`native_build_mir_shard_count`, `src/app/cli/native_build_main.spl`), so
  each worker claims ~1516 of 3031 modules.
- Each MIR shard worker runs its own parse+HIR and starts MIR at ~19.3 GiB.
- A shard worker keeps every claimed module's MIR in `ctx.mir_modules` until
  the whole claim loop ends (`aot_compile_mir_shard_v1`,
  `src/compiler/80.driver/driver_aot_pipeline.spl`, `begin(0)` = staging
  off). Evicting would not help: the native runtime has no collector
  (`native_staged_codegen.spl` header, probe P0: 0 of 2001 allocations
  reclaimed); process exit is the only release.
- Measured growth: ~11 MiB RSS per claimed module (largest-first claim order).
  2 x (19.3 + 1516 x ~0.011) GiB does not fit 52 GiB at any point past ~1100.

## In-process measurement (probe build, 2026-11-06)

Probe binary = `a720cb10557` + a retained-root dump (local only, not landed),
`native-build src/app/cli/bootstrap_main.spl` (1571 modules), in process,
`SIMPLE_NATIVE_STAGED_CODEGEN_BATCH=0`, `MemoryMax=32G`,
`SIMPLE_MIR_SECTION_PROFILE_FILE` rows per lowering section:

| modules lowered | runtime heap_live (MiB) | RSS (MiB) |
|---|---|---|
| 100 | 2617 | 11930 |
| 200 | 2761 | 13058 |
| 300 | 2903 | 13694 |

- heap_live grows 1.4 MiB per module; RSS grows ~8.8 MiB per module.
- Every `MirLowering` field root (`transient_owner.spl` inventory) is flat
  between position 50 and 100 (largest: `provider_enum_row_variants` 21 MiB,
  `rti.rows_by_key` 5.8 MiB, `callable_link_names` 5.5 MiB).
- Per-module retained heap (s5 minus p0) has a fixed floor of ~955 KiB even
  for one-line facade modules (`app/io/time_ops.spl`), plus a size term
  (`bootstrap_main.spl` 7 MiB, `driver_aot_native_output.spl` 7 MiB).
  A trivial module allocates ~12 MiB in the provider sections (p5a provider
  loop 6.4 MiB, p5 layouts 2.1 MiB, p6 1.4 MiB, p1 1.0 MiB) and the scope end
  frees ~11.1 MiB.

## Mitigation landed

`bootstrap_phase_c_run_tool_build` exports `SIMPLE_MIR_SHARD_COUNT=8` for the
full-tool rows (scoped to the call, like `SIMPLE_FILE_WORKERS=0`; an explicit
caller value wins). Each worker then claims at most ~380 modules: about
19.3 + 380 x 0.011 = 23.5 GiB, two concurrent workers about 47 GiB. Pinned by
`scripts/bootstrap/tests/phase-c-backend-commands-test.shs`.

## Not fixed

1. The ~955 KiB fixed per-module retained floor (closure-sized provider
   tables surviving each module's transient scope).
2. RSS growing ~6x faster than runtime heap_live (untracked or fragmented
   bytes after scope end).
3. The 19.3 GiB per-worker HIR floor: every MIR shard worker rebuilds the
   whole HIR before claiming a module.
4. A single cold MIR shard worker (`--threads 1`, no HIR shards) SIGSEGVs
   during in-process HIR at `compiler.common.error_codes` (2868/3060),
   `status=CRASH exit=-139`, on the run-10 Stage 2 binary `43f9a6fc68ac`.
