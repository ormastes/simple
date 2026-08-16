# Feature Expert: Secure Pure-Simple Servers

## Role

Own feature knowledge for the Phase-6 secure web/database server closure. Keep
claims tied to the canonical Pure-Simple entrypoints and retained executable
evidence; never substitute benchmarks, memory transports, raw-source launchers,
the Rust seed, or foreign servers.

## Canonical Links

- Guide: [pure_simple_servers.md](../../../07_guide/lib/pure_simple_servers.md)
- Ledger: `doc/03_plan/agent_tasks/simpleos_production_master_plan_completion_status.md`
- Acceptance state: `.spipe/secure_pure_simple_servers/state.md`
- System-test plan: [secure_pure_simple_servers.md](../../../03_plan/sys_test/secure_pure_simple_servers.md)
- Executable web SSpec: `test/03_system/web/server/secure_pure_simple_web_server_spec.spl`
- Web operator manual: [secure_pure_simple_web_server_spec.md](../../../06_spec/03_system/web/server/secure_pure_simple_web_server_spec.md)
- Shared HTTP policy: `src/lib/common/net/http_core.spl`
- Web: `src/lib/nogc_sync_mut/http_server/`
- DB: `src/lib/nogc_sync_mut/database/server/`
- Database companion expert: [database_sql](../database_sql/skill.md)
- Transport/security layer expert: [server_transport_security](../../layer_expert/server_transport_security/skill.md)

## Completion Contract

The web path must prove real accept -> bounded parse -> security policy ->
router -> bounded complete write -> close. Shared `http_core` ownership does
not replace that socket-path proof. TLS must reject missing/invalid material
rather than downgrade. Today `tls_server_accept` fails closed because GAP-TLS-3
still blocks encrypted transport. The DB path includes an owned bounded listener, authenticated `OPEN`,
single authoritative mutation ownership, invisible durability P3/P4, durable
versions and reconnect-safe commit identity, and bounded capability-preserving
batch/range operations. The continuation UTF-8 and real-loopback lifecycle
fixtures are authored but unexecuted. None is credited until focused scenarios
pass.

## Evidence Rules

Every AC-9 scenario needs an absolute oracle, deliberate-red calibration,
REQ/AC traceability, and no placeholder pass. Every changed SSpec needs one
`sspec-maintain scan` and a `0 stubs` operator-readable `doc/06_spec` mirror.
Run focused checks once on an admitted Stage-4 CLI, then the whole interpreter
suite once for release. GAP-TLS-3 and the unhealthy CLI are active blockers.
Use the exact deferred order in
`doc/03_plan/sys_test/secure_pure_simple_servers.md`; historical seed-banner
runs, hand-authored mirrors, and static fixtures are not substitutes.

For the REQ-002 response-framing lane, preserve three visible operator flows:
valid application response -> server-owned serialization -> canonical complete
body; conflicting/control-bearing fields -> server-owned serialization ->
override/injection rejection; and production listener -> hostile handler ->
complete real-loopback wire response. Use built-in matchers and exact positive,
edge/error, and integration assertions. The server writer alone owns
`Content-Length`, `Transfer-Encoding`, and `Connection`.

Never execute this lane with the Rust seed or an unreceipted binary. Without an
adjacent admission receipt for the current-source pure-Simple Stage-4 full CLI,
record `TEST_BLOCKED` and leave runtime, `sspec-maintain`, and docgen deferred.
The executable remains under `test/03_system`; `doc/06_spec` receives Markdown
manuals only.

## Update Rule

Update this lane expert, guide, plan, manual, and `.spipe` state whenever a
response-framing interface, blocker, scenario, evidence command, or completion
mark changes. Do not edit a shared global or another pane's expert skill merely
to record this lane-local continuation.
