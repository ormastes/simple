# Secure Pure-Simple Servers Design — TLDR

- `SecureServerPolicy` validates immutable web limits before bind.
- Production web streams require owned encryption; GAP-TLS-3 currently blocks them.
- Plaintext development is explicit and follows the same bounded dispatch path.
- `DbListener` owns capacity, accept, cleanup, and shutdown lifecycle.
- `DbTransport` bounds framing and makes close idempotent.
- `AuthenticatedPrincipal` is produced before capability lookup.
- One authoritative store owner spans reads, P3 apply, P4 persist, and outcome.
- Durable row versions and commit fingerprints survive reopen.
- Repeated matching `CommitIdentity` returns its recorded result without reapply.
- `BoundedQuery` prevalidates capabilities and limits before overlay mutation.
- Range results merge the caller overlay, sort by stable key, and cap response bytes.
- Evidence uses loopback, peer-reader, reopened-file, and bind-after-shutdown oracles.
- Primary flow names and checker names are fixed in the full design.
- Next: implement remaining gaps and execute `doc/03_plan/sys_test/secure_pure_simple_servers.md`.
