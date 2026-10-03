# Item 4 diagnostic build: source inventory cold-init exceeds 120-second bound

Date: 2026-10-03. Status: OPEN, diagnostic infrastructure blocker.
Owner: compiler source-inventory/native-build path; discovered by item-4 linker work.
No linker runtime failure, admitted compiler failure, or release verdict is asserted.

## Observed evidence

Source HEAD: `cacfb79a678643991bdac6d82437f1626c843d2d` in the isolated
`C:/dev/simple-item4-linker-dev-20261003` worktree, based on `release/1.0`.
The pure-Simple Stage 2 diagnostic candidate was built from
`78d5a1cd7768f70cc42a56888ef3a799823bd738`; SHA-256:
`aaf13da5942425e19b1aba2ed4b6d272687de1d4710ad7200ed0621d96990879`.
Its provenance is explicitly UNADMITTED. Bounded `--help` exited zero and
identified the Simple-built bootstrap compiler with native-build support.

The probe is `test/fixtures/linker/diagnostic/item4_linker_probe.spl`. It imports
the actual linker/parser and returns nonzero for incorrect NUL-interpreter or
overflow-table behavior. Native-build uses one thread, the LLVM backend,
`--source src/compiler --source src/lib --source src/app --entry-closure`, and
session-owned output/cache beneath `build/item4-diagnostic/`. Canonical SCV
inventory lives in this worktree's `build/scv`; no shared-worktree cache is used.

Three bounded attempts, preserving the actual progression:

1. Entry under `build/`: rejected with `source-inventory-scope-unsupported`.
   Source inspection established that inventory admits the src/test families.
2. Identical probe under `test/fixtures/`: rejected with
   `compile-event-journal-missing`, requesting `SIMPLE_SCV_INVENTORY_COLD_INIT=1`.
3. Canonical cold initialization enabled: exceeded the 120-second whole-job
   bound. Wrapper receipt records timeout/exit 124 and `cleanup_status=reaped`.
   The log contains the workaround-coverage note, but no completed probe build.
   `build/scv/compile-events/refresh.lock` appeared; no completed inventory
   artifact was observed there. No probe executable or runtime result exists.

Evidence is retained locally in `build/item4-diagnostic/`:
`help-provenance.env`, `probe-build.log`, `probe-build-test-root.log`,
`probe-build-cold-init.log`, `probe-build-cold-init.receipt.env`,
`probe-build-cold-init-inputs.sha256`, and `probe-build-cold-init-head.txt`.
The existing bounded Windows process wrapper owns timeout/cleanup. No admission
guard was disabled and no Rust-seed test fallback was used.

## Required next investigation

Inspect the captured inventory progress/lock ownership and source-inventory
implementation before another build. A leftover lock is not evidence of a live
process; revalidate ownership before any recovery. Preserve existing cache and
other sessions. Determine whether the cost is normal cold hashing, lock waiting,
or another inventory path; current evidence does not distinguish those causes.
Use a measured, explicitly scoped inventory operation before reattempting the
probe. Do not call the 120-second diagnostic limit a production performance SLO.

Resume linker behavioral verification only after a usable execution route exists.
Even a successful unadmitted probe is diagnostic-only; modern SSpec, core/MCP,
manual-generation and release gates still require their admitted runtimes.
