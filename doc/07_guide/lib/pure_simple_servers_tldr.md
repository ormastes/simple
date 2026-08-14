# Secure Pure-Simple Servers — TLDR

- Canonical guide: [pure_simple_servers.md](pure_simple_servers.md).
- Web owner: `src/lib/nogc_sync_mut/http_server/`.
- DB owner: `src/lib/nogc_sync_mut/database/server/`.
- Web plaintext development is capability-gated and uses peer identity, bounded parsing, and default security headers.
- HTTPS is blocked by `GAP-TLS-3` and missing typed DER key-pair validation.
- Every current TLS accept failure closes its owned TCP stream without fallback.
- Startup returns a typed result; only audited loopback callers mint plaintext authority.
- Parser truncation detection matches the native line API's 4096-byte boundary.
- Shared atomic admission caps connections at 128 by default and rejects before spawn.
- DB `OPEN` requires principal plus credential, compares 64 digest characters,
  and uses one exact missing/wrong/unknown failure frame.
- DB has owned bounded TCP/memory transports with sequential state ownership.
- Durable versions/commit IDs and bounded capability-checked batch/range are implemented.
- Final requirements/NFRs, architecture/design, plans, scenarios, and manuals exist.
- Runtime evidence and `sspec-maintain`/docgen remain blocked by the unhealthy Stage-4 CLI.
- The staged Stage-2 binary identifies successfully; unverified observations say `check`/`test` return `unknown command`.
- An unverified observation says its one-shot native web-spec build stopped at HIR `ANY.error?`; no executable was produced.
- DB exposes concrete `DbListener`/`TcpDbListener`, `CommitIdentity`, and
  `BoundedQuery` contracts; production and scripted response paths share the
  encoded-byte bound, with runtime TCP proof still open.
- Benchmarks and legacy mirrored specs are not production acceptance evidence.
- Run each focused criterion once after admitting a healthy Stage-4 self-hosted CLI.
- Final release gate: `bin/simple test test --whole --mode=interpreter`.
- Ledger: `doc/03_plan/agent_tasks/simpleos_production_master_plan_completion_status.md`.
