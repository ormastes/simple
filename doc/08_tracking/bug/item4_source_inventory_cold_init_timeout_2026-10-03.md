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

## 2026-10-04 evidence-led revalidation

The original receipt still records timeout 124 with the Windows job reaped.
Its captured output is only the workaround-coverage note; it does not identify
the inventory phase consuming the bound. The retained refresh.lock is empty,
and no matching compiler process was observed for that old worktree during
this audit. No lock, cache or failed receipt was removed and no old probe was
restarted. The three-attempt diagnostic cap remains in force.

The canonical `scripts/bootstrap/bootstrap-scv-prime.shs` separates cold
inventory priming from warm admission and documents a much longer measured
Windows snapshot initialization. That observation does not prove the cause of
this older timeout or turn its 120-second limit into a product performance SLO.

Newer independent evidence exists under
`C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/`.
`cross-backend-llvm-hello1/verified-hello.json` records
`state=diagnostic-hello-pass`, source
`9737d1217bc44439b56bba6c2ef16faaff51bd20`, and producer
`p2-post-bool-link-repair2/cranelift/compiler.exe`, SHA256
`776ce2a1b8b0f92d44e5dd70b5fac365ba96187f76cfa0ffc2c5bdcac8fdae40`.
This is a retained-object diagnostic relink with `admitted=false`; it does not
establish an admitted full CLI or test runner. The Hello result records actual
compile/run success; binary presence or `--help` was not substituted for it.

The separately owned full-CLI and test-runner jobs under
`phase34-post-link4/cranelift/` had live owner/collector pairs
64728/34464 and 37596/22612 at this audit, with no usable product executable.
These are point-in-time process observations, not permanent wait handles.
Their processes and writable caches were preserved. Summary rows may reference
retained earlier attempts, so aggregate counts alone are not current-attempt
completion evidence. Actual fatal diagnostics in the full-CLI owner's
`.build.log.tmp.34464` instead identify actionable source failures, including
the separately tracked loader compatibility-helper calls.

The linker execution recipe is now
`doc/06_spec/03_system/app/compiler/feature/item4_linker_execution_gate.md`.
Its explicit native path still needs generated-entry admission and a qualified
full CLI. Corrected commands and the newer Hello receipt do not close this bug
or establish linker behavioral verification.
