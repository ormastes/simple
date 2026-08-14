# Secure Pure-Simple Servers — TLDR

- Canonical guide: [pure_simple_servers.md](pure_simple_servers.md).
- Web owner: `src/lib/nogc_sync_mut/http_server/`.
- DB owner: `src/lib/nogc_sync_mut/database/server/`.
- Web plaintext development mode binds and accepts through bounded secure parsing.
- HTTPS is not production-ready: `tls_server_accept` fails closed on `GAP-TLS-3`.
- DB `OPEN` now requires principal plus credential and denies by default.
- DB has owned bounded TCP/memory transports with sequential state ownership.
- Durable versions/commit IDs and bounded capability-checked batch/range are implemented.
- Final requirements/NFRs, architecture/design, plans, scenarios, and manuals exist.
- Runtime evidence and `sspec-maintain`/docgen remain blocked by the unhealthy Stage-4 CLI.
- Benchmarks and legacy mirrored specs are not production acceptance evidence.
- Run each focused criterion once after admitting a healthy Stage-4 self-hosted CLI.
- Final release gate: `bin/simple test test --whole --mode=interpreter`.
- Ledger: `doc/03_plan/agent_tasks/simpleos_production_master_plan_completion_status.md`.
