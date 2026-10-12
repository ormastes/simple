# MIR progress counted failed modules as successes

Status: source candidate; pure accounting native PASS, complete driver/compiler integration uncompiled.

Release17c1347 includes the common accounting helpers and fixtures, but its
actual logger/AOT/module-loop call sites were still unchanged. The Windows
continuation now connects those actual paths: each scheduled module records
new fatal diagnostics/context errors/ICE once, MIR success is
processed-minus-cached-minus-failed in console/events/snapshot, and terminal
failure reuses only a matching completed parent row. Partial or unclassified
counts remain unknown. Source review passed; actual compiled behavior remains
unverified.

An independent logger build using older admitted compiler17d1a40 reached56
HIR stores and a completed worker, then exceeded the unchanged5,859,375 KiB
enforced process-tree cap (peak5,916,480 KiB, jobs1, exit88/quiescent1). No
object was produced and link/run were not attempted. Exact input hashes stayed
unchanged; evidence is retained at
`C:/dev/simple-phase3-bootstrap-evidence/attempt14/logger-diagnostic/final-summary.env`.
This failure does not qualify the logger or the new Phase3 producer.

Reproducer: committed MCP candidate c77645159 with P2 runtime-only successor 027c7579 produces two fatal MIR errors (storage_roots/resolver.spl177 Result.map; common/json/array_ops.spl479 tuple iteration) but the final processed-module row says done141 succeeded141 failed0. The later AOT failure row says unknown counts and failed1, not the two failed modules. Evidence /mnt/c/Temp/simple-manual-lanes-20261011/p2-mcp-qualified-sites-runtime/compile.log. No object published and terminal exit1; this is a reporting bug, not a passing compilation.

Cause: the direct module loop deferred fatal diagnostic collection until after its progress rows and supplied hardcoded failed0. The common logger calculated succeeded=done-cached, omitting failures. The AOT failure branch invented one failure without using the classified module count.

Repair: classify only new fatal diagnostics (using the existing fatal predicate) and context errors once per processed module; warnings remain successful. Report the failed count before the deferred aggregate error collection. MIR successes exclude both cached and failed units (other legacy stage callers already exclude failed units from done and retain their existing accounting); inconsistent or unknown counts remain unknown. Preserve the latest parent-owned phase accounting when emitting the terminal failure event; if no known failure count exists, emit unknown rather than a fabricated zero or one. This uses the logging owner's existing per-process phase scope, not shared worker accounting.

Regression: test/fixtures/bootstrap/mir_progress_accounting_probe.spl imports the actual shared compiler accounting functions. Nine native assertions exercise mixed module outcomes, cached work, exact141/139/2 totals, unknown failure counts, impossible counts, unknown totals, and zero/all-success boundaries. Actual admitted source snapshot bound in /mnt/c/Temp/simple-manual-lanes-20261011/p2-mir-progress-accounting/actual-source-binding.json. Compile0/26.500s/object3224B; strict paired runtime594f/backfill935f link0, ELF2794928B; run0/stdout0/stderr0. No green re-run performed.

Remaining: three driver source integrations have not been compiled; full CLI/compiler check gates unavailable because current bootstrap compiler entries lack check/test dispatch. No full MCP/runner build or release merge was attempted for this reporting fix.

Review correction: persisted BuildProgressSnapshot.compiled_files now uses the same MIR-success calculation (139 for done141/failed2), with cached modules reported separately. Other legacy phase contracts are preserved. Terminal accounting reuses a classified count only if phase and unit kind match and all planned modules were accounted; interrupted chunks produce unknown done/failure counts instead of a stale earlier chunk. Unknown queued/remaining counts remain unknown, and a failed snapshot still carries an error summary even when count is unknown. Logging state is parent-owned and process-local; workers do not share the counters, and the AOT start row resets prior phase accounting.

Separate snapshot/early-abort native regression: test/fixtures/bootstrap/mir_progress_snapshot_contract_probe.spl imports actual shared functions and passed eight new assertions (compiled-vs-cached-vs-failed, other-phase preservation, completed failure totals, partial/empty/unknown classification). Compile0/24.476s/object4448B; strict paired runtime594f/backfill935f link0/ELF2795136B; run0/stdout0/stderr0. Evidence /mnt/c/Temp/simple-manual-lanes-20261011/p2-mir-progress-snapshot-contract/{receipt.json,link-run-receipt.json,actual-source-binding.json}. The previous nine already-passing assertions were not rerun. Full driver integration remains uncompiled; these fixtures do not qualify the compiler or application CLI.

Final reporting integration criterion (third cycle, stopped): test/fixtures/bootstrap/mir_progress_logger_probe.spl calls the actual driver logger for complete classified failure, different unit kind, and partial abort. The logger owner and its real host/library closure compiled natively (exit0/115.176s/object1,025,096B; actual SCV snapshot byte-bound). Strict paired archive594f/935f linking failed with four undefined providers: WINDOWS_REDIRECTED_TOKEN_BASE imported source global, rt_print_err, rt_debug_exit_success, rt_perf_dump_sdn. No provider stub or incompatible runtime substitute was used. The fixture never executed, so stdout/persisted snapshot assertions remain unqualified. The complete lowering/AOT owners are still uncompiled. Evidence /mnt/c/Temp/simple-manual-lanes-20261011/p2-mir-progress-actual-logger/{receipt.json,link-run-receipt.json,link-failure-summary.json,actual-source-binding.json}. No fourth reporting retry.
