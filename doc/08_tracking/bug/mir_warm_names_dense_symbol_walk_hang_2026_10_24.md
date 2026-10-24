# MIR warm-names walks 0..next_symbol_id (2^50) and never finishes (2026-10-24)

Status: FIXED (root cause; not a workaround) — pending Stage-2 redeploy proof.
Explains: `self_hosted_mir_lowering_pathologically_slow_2026_10_22.md` (the
"RSS pinned at ~33.3 GB, never produces objects" symptom).

## Symptom

Self-hosted `native-build` of any closure with at least one mono
specialization stops right after `aot:mir_setup:warm_names:start`, at 98% CPU,
with flat RSS, and never lowers a single MIR module. On the full
`bootstrap_main` closure (1471 modules) the flat RSS is ~33.3 GB, so it reads as
a memory pin; it is really the post-mono resident set frozen at one program
point while a CPU loop runs.

## Evidence (producer stage2 sha256 c7d429f2a02f3b4e…, aarch64)

- `hello.spl` (1 module, `specializations=0`): passes warm_names, links, 49 s.
- `pa.spl` (`use compiler.common.driver_core_types`, 204 modules,
  `specializations=15`): reaches warm_names at +164 s, then >8 min stalled at
  2.97 GB RSS (two independent runs), `warm_names:done` never printed.
- 4/4 gdb SIGINT samples of the worker: `driver_warm_mir_logical_names_v1` →
  `SymbolTable.symbol_defining_module_scalar_raw` → `rt_dict_get`/`rt_contains`.
- Breakpoint on `symbol_defining_module_scalar_raw`, `$x1` (raw id) =
  447029164, 447029165, 447029166 ~55 s into the loop — far past any dense
  symbol range, climbing by 1 at ~10^7/s.

## Root cause

`src/compiler/80.driver/driver_pipeline_lowering.spl:241` (added in
45a8a95e67b, 2026-10-19) walks `raw_id` from 0 to
`module.symbols.next_symbol_id`, assuming ids are dense. They are not:
`register_preserved_symbol` (`20.hir/hir_symbol_table_methods.spl:109`) raises
`next_symbol_id` past every preserved id, and mono specializations are
registered at `MONO_SYMBOL_BASE = 2^50`
(`40.mono/monomorphize_integration.spl:81`,
`80.driver/cache/hir_mono_replay_selection_v1.spl:106-113`). One module with a
specialization makes the walk ~2^50 iterations. The selective MIR worker had
the same loop (`driver_mir_selective_worker_v1.spl:247`).

## Fix

Both loops now iterate `module.symbols.symbols.keys()` (the real id set). The
cost is one `[i64]` keys array per module allocated at state 0 (immortal),
i.e. O(total symbols) words once — measured below.

Regression spec: `test/01_unit/compiler/80.driver/mir_warm_names_sparse_symbol_ids_spec.spl`
(UNEXECUTED: no full-CLI `simple test` binary on this host).

## Growth law (before)

Not a MIR-phase leak: RSS at MIR entry grows ~linearly with closure size
(2.5 GB at 1 module, 3.0 GB at 204, ~33 GB at 1471 ≈ 21 MB/module above the
204-module point), and MIR then never runs. Whether MIR lowering itself
retains per module is unmeasured until this hang is gone (see the
2026-10-20 retention record for the bootstrap-fixed lane).
