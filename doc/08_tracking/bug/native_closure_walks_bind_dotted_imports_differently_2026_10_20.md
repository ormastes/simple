# Native closure walks bind imports differently (coordinator vs snapshot-root workers; spelling dedupe)

- Status: OPEN
- Date: 2026-10-20
- Platform: aarch64-unknown-linux-gnu
- Severity: P2

## Observation

Edge-logging diagnostic relink of Stage 2 (release_phase3 + the bare-sibling
resolver fix), Stage 3 phase 1 on bootstrap_main: the coordinator walk (no
source roots) closes over 1352 modules, each HIR shard worker walk (snapshot
source roots app/lib/compiler/os/plugins) over 1353. These spellings bind to
different files in the two walks:

- `common.string_builder`: src/app/common/string_builder.spl vs
  src/lib/common/string_builder.spl
- `compiler.mir_opt.optimization_passes`, `compiler.mir_opt.optimizer_manifest`:
  src/compiler/60.mir_opt/*.spl vs src/lib/compiler/mir_opt/*.spl

Workers then lower different code for the same module name than the
coordinator selected.

Separately, the walker de-duplicates imports by spelling for the whole walk
(`closure_seen_mods`, driver_source_pipeline_loading.spl ~976/1060): a bare
`types` or `mod` is resolved once, for the first importer, and other
packages' same-named siblings are not added (reported by Opus review of the
bare-sibling fix).

## Next step

Key de-duplication on the resolved file, not the spelling, and make both
walks use one resolution order; then assert both walks yield the same module
set (a parity check in the Stage 3 coordinator).
