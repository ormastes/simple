# Secure Pure-Simple Web and Database Servers

This guide is the canonical operator/developer map for the Phase-6 server
lane. It describes current repository state, not an advertised production
claim. The lane remains blocked until its executable evidence passes on an
admitted Stage-4 self-hosted CLI.

## Ownership and Reachability

| Surface | Canonical owner | Current reachability |
|---|---|---|
| Synchronous HTTP listener and routing | `src/lib/nogc_sync_mut/http_server/{server,parser,router,response,static_file}.spl` | The explicit plaintext-development listener binds, accepts, performs bounded parsing, dispatches, writes, and closes; runtime evidence remains blocked. |
| Asynchronous HTTP stack | `src/lib/nogc_async_mut/http_server/` | Separate stack; do not use its benchmark fixtures as proof for the synchronous production entrypoint. |
| HTTPS composition | `src/lib/nogc_sync_mut/http_server/tls_server.spl` | **Not production reachable:** missing/invalid material and absent encrypted transport fail closed; GAP-TLS-3 still blocks HTTPS. |
| Database protocol and capsule | `src/lib/nogc_sync_mut/database/server/` | Pure-Simple bounded TCP + memory transports, authenticated sessions, sequential state owner, capability/transaction/durability tier, and bounded batch/range surface; runtime evidence remains blocked. |
| Database persistent store | `src/lib/nogc_sync_mut/database/core.spl` and `atomic.spl` | `durable_commit` persists through `SdnDatabase.save()` before acknowledgement. |

Production wrappers must execute cached compiled artifacts. A benchmark,
in-memory transport, Rust seed, raw-source launcher, or foreign server is not
equivalent evidence for either canonical path.

## Security and Durability Contracts

HTTP must reject unsafe input before router dispatch: oversized request lines,
header counts/lines or bodies; malformed or conflicting framing; unsupported
transfer coding; traversal; exhausted read/keep-alive budgets; and timeout.
Security headers and request identity must be applied on the same real accepted
connection path. TLS startup must fail closed when certificate/key material is
missing or invalid. Until the TLS gaps named in `tls_server.spl` are repaired,
the guide must not describe HTTPS as production-ready.

Database `OPEN` requires both `as=<principal>` and `credential=<secret>`.
`CapabilityTable.register_authenticated` refuses empty credentials, and
`authenticate` performs a full padded comparison; failures use the stable
`auth` response and must not echo or log secrets. All later operations are
session-scoped and deny by default unless the captured capability explicitly
grants the table/access pair.

The established commit order is precheck, capture undo state, apply in memory,
persist with `save()`, then acknowledge. The implementation now uses a
sequential capacity-one mutation owner, persists row-version fields and commit
receipts in the same atomic save, and bounds batch/range requests and responses.
These claims remain implementation-handoff status until focused scenarios
execute on an admitted Stage-4 CLI.

## Evidence Map

- Acceptance ledger and resume blocker:
  `doc/03_plan/agent_tasks/simpleos_production_master_plan_completion_status.md`
- SPipe acceptance criteria: `.spipe/secure_pure_simple_servers/state.md`
- Existing web designs:
  `doc/05_design/ui/web/simple_web_server_lib_api.md`,
  `simple_web_server_split.md`, and `simple_web_server_example.md`
- Database owner map and durability caveats:
  `doc/00_llm_process/feature_expert/database_sql/skill.md`
- Existing executable DB scenarios:
  `test/03_system/database/server/db_server_tier_spec.spl` and
  `db_durability_spec.spl` (the mirrored legacy `test/system/` copies are not
  separate acceptance evidence).
- Final requirements, NFRs, architecture, detail design, test plan, and agent
  plan share the slug `secure_pure_simple_servers` in their canonical trees.
- Focused modern web and DB scenarios and mirrored manuals live under
  `test/03_system/{web/server,database/server}/` and
  `doc/06_spec/03_system/{web/server,database/server}/`.
- TLS blockers GAP-TLS-1..3 have matching open records under
  `doc/08_tracking/bug/`; GAP-TLS-3 blocks production HTTPS completion.

## Focused Verification (Run Once After CLI Admission)

Use the admitted self-hosted binary, record its path and hash, and do not repeat
an unchanged passing command. The focused evidence inventory is:

```sh
bin/simple check src/lib/nogc_sync_mut/http_server
bin/simple check src/lib/nogc_sync_mut/database/server
bin/simple lint <changed-simple-files>
bin/simple test test/03_system/database/server/db_server_tier_spec.spl --mode=interpreter
bin/simple test test/03_system/database/server/db_durability_spec.spl --mode=interpreter
bin/simple test test/03_system/database/server/secure_pure_simple_db_server_spec.spl --mode=interpreter
bin/simple test test/03_system/web/server/secure_pure_simple_web_server_spec.spl --mode=interpreter
bin/simple duplicate-check src/lib/nogc_sync_mut/http_server --mode token --min-lines 5
bin/simple duplicate-check src/lib/nogc_sync_mut/database/server --mode token --min-lines 5
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
find doc/06_spec -name '*_spec.spl' -print
bin/simple test test --whole --mode=interpreter
```

Each changed SSpec also needs one `sspec-maintain scan`,
REQ/AC traceability, deliberate-red calibration, `0 stubs`, and an operator-
readable mirrored Markdown manual. The whole interpreter suite is the final
release-bound gate, not a substitute for the focused scenarios.

## Update Rule

When server interfaces, policies, specs, evidence commands, or blockers change,
update this guide, its TLDR, both expert skills, and the Phase-6 ledger in the
same change. File every discovered unresolved implementation defect under
`doc/08_tracking/bug/` with file/line and unblock condition.
