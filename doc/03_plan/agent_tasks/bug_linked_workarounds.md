# Agent plan: bug-linked workarounds

User-requested Astra owns research, design, implementation integration, and
final review. Source edits live in the isolated workaround checkout.

| Lane | Owner | Scope |
|---|---|---|
| Integration | Astra lead | Pure model/parser, check-dbs integration, build boundary, executable tests, final review |
| Persistence | Store agent | Text index maintenance, bounded discovery, locking and atomic publication |
| Documentation | Docs agent | Requirements/research/design, bootstrap/debug skills, guide, host SPipe wiki |
| Merge | Astra lead | Review selected diffs; preserve all unrelated concurrent work |
| Lower-model sidecars | N/A | No broad generated-manual delegation |

Shared contract: `@workaround bug=<id> [recover=<hex>] [reason=<text>]`;
`.simple/workarounds.sdn`; `check-dbs --fullscan bugs`; query-only ordinary
bug checks. Reason is optional. Recovery never mutates source automatically.

Tests use real parser/index/join assertions. Fail-fast helpers, if needed,
must fail until implemented. Verify each acceptance criterion once per unchanged
implementation; maximum three fix/verify cycles. Stop when the requested
artifacts and focused evidence are complete; report runtime limitations.
