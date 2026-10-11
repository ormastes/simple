# MIR progress counted failed modules as successes

Status: source candidate; pure accounting native PASS, complete driver/compiler integration uncompiled.

Reproducer: committed MCP candidate c77645159 with P2 runtime-only successor 027c7579 produces two fatal MIR errors (storage_roots/resolver.spl177 Result.map; common/json/array_ops.spl479 tuple iteration) but the final processed-module row says done141 succeeded141 failed0. The later AOT failure row says unknown counts and failed1, not the two failed modules. Evidence /mnt/c/Temp/simple-manual-lanes-20261011/p2-mcp-qualified-sites-runtime/compile.log. No object published and terminal exit1; this is a reporting bug, not a passing compilation.

Cause: the direct module loop deferred fatal diagnostic collection until after its progress rows and supplied hardcoded failed0. The common logger calculated succeeded=done-cached, omitting failures. The AOT failure branch invented one failure without using the classified module count.

Repair: classify only new fatal diagnostics (using the existing fatal predicate) and context errors once per processed module; warnings remain successful. Report the failed count before the deferred aggregate error collection. MIR successes exclude both cached and failed units (other legacy stage callers already exclude failed units from done and retain their existing accounting); inconsistent or unknown counts remain unknown. Preserve the latest parent-owned phase accounting when emitting the terminal failure event; if no known failure count exists, emit unknown rather than a fabricated zero or one. This uses the logging owner's existing per-process phase scope, not shared worker accounting.

Regression: test/fixtures/bootstrap/mir_progress_accounting_probe.spl imports the actual shared compiler accounting functions. Nine native assertions exercise mixed module outcomes, cached work, exact141/139/2 totals, unknown failure counts, impossible counts, unknown totals, and zero/all-success boundaries. Actual admitted source snapshot bound in /mnt/c/Temp/simple-manual-lanes-20261011/p2-mir-progress-accounting/actual-source-binding.json. Compile0/26.500s/object3224B; strict paired runtime594f/backfill935f link0, ELF2794928B; run0/stdout0/stderr0. No green re-run performed.

Remaining: three driver source integrations have not been compiled; full CLI/compiler check gates unavailable because current bootstrap compiler entries lack check/test dispatch. No full MCP/runner build or release merge was attempted for this reporting fix.
