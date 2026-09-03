# macOS M2/M3 incremental reuse audit — 2026-09-03

Scope: production compiler cache/driver reverse references and Phase 2 to
Phase 3 compatibility. Native producer qualification is deliberately excluded.

The audit found and repaired one production gap: `Modified` sources previously
followed all ten projection families even when their exported interface was
unchanged. Cache rows now retain the source-owned interface digest. A matching
current digest selects only the proven module/SCC artifact and emitted-symbol
relocation families; an interface change, legacy row, unreadable source, or
unknown generation remains conservative. The worklist continues to its fixed
point, preserving SCC and transitive closure.

`module-scc-artifact` now means self-artifact identity or an explicitly
published same-SCC peer. Build-cache `dependencies` publish only ordinary
`direct-import-export` consumption; they no longer manufacture SCC edges.
Thus a private-body edit rebuilds the changed producer and follows relocation
or proven SCC contracts without recompiling an ordinary reverse dependent.
The production publisher is `package_scc_consume_index_schedule_v1`: after its
declared condensation schedule validates, it publishes every source pair in
each scheduled index SCC. Module and package identities become aliases of
their source identities, and peer evidence is a SHA-256 digest of the declared
SCC identity plus sorted source identities.

Phase 2 to Phase 3 frontend and native-object consumers now emit a stable
`simple-phase2-phase3-reuse-ledger-v1` summary with exact hit and rejection
counts after their per-item attributed decisions. The manifest still binds the
immutable M2 receipt digest, owner/root generations, exact key frame, consumer,
provider, target, schema, producer where native, and artifact digest. Clean vs
reused normalization remains limited to CRLF plus documented elapsed/RSS rows.

Portable production and 16/16 mutation checks passed. Focused SPipe and the
optimizer were each attempted once with the repo wrapper and were blocked
before execution because the referenced admitted
`bin/release/x86_64-unknown-linux-gnu/simple` artifact is absent. No Rust seed,
copied binary, native receipt, or producer proof was substituted.

Still blocked: native arm64 and x86_64 Phase 2/3 producer artifacts and
receipts, native zero-work/zero-link observations, native clean-vs-reused
output artifacts, full CLI/test-runner/MCP/LSP qualification, and admitted
architecture-matched performance baselines.
