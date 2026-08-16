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

## Update Rule

Update this skill, the guide/TLDR, layer expert, and Phase-6 ledger whenever an
interface, blocker, scenario, evidence command, or completion mark changes.
