# Secure Pure-Simple Web and Database Servers

This guide is the canonical operator/developer map for the Phase-6 server
lane. It describes current repository state, not an advertised production
claim. The lane remains blocked until its executable evidence passes on an
admitted Stage-4 self-hosted CLI.

## Ownership and Reachability

| Surface | Canonical owner | Current reachability |
|---|---|---|
| Synchronous HTTP listener and routing | `src/lib/nogc_sync_mut/http_server/{server,parser,router,response,static_file}.spl` | The capability-gated plaintext-development listener binds, accepts, obtains peer identity, performs bounded parsing, dispatches, adds default security headers, writes, and closes; runtime evidence remains blocked. |
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

Plaintext requires both `SecureServerPolicy.plaintext_dev(capability)` and
`start_plaintext(capability)`, where the capability is minted from a non-empty
audit reason. `start()` never opens plaintext. Request lines are measured before
whitespace normalization and must have exactly three SP-separated components;
EOF before the request-line/header terminator rejects as incomplete framing.
Failure to obtain the socket peer address also closes before dispatch. Default
CSP, nosniff, frame-denial, and referrer headers are applied before writing;
HSTS is reserved for a genuinely encrypted connection.

`SecureServerPolicy.max_connections` is positive and defaults to 128. A shared
`ConnectionAdmission` atomic handle claims a slot before thread spawn, closes
boundary+1 immediately, and releases after either threaded or synchronous handler
completion. Worker copies retain the atomic handle, not a copied counter.
The handler wrapper registers release with `defer` before application dispatch,
so early return or unwinding cannot strand capacity.

The present TLS configuration check recognizes only a hex-DER envelope. The
existing certificate owner can parse PEM X.509, but exposes no typed parser for
the configured hex-DER private key and no certificate/private-key correspondence
check. Alongside GAP-TLS-3, that exact validation gap blocks production TLS.
`tls_server_accept` closes its owned TCP stream on every current failure.

All synchronous `SimpleHttpServer` startup APIs return `Result<(), text>`.
The example and loopback-only LLM Caret callers handle that result explicitly;
non-loopback messaging hosts preserve production intent by calling `start()`
and receiving the TLS-required error rather than minting plaintext authority.
The native line-reader boundary exposed to this parser is a 4096-byte buffer
(4095 payload bytes plus terminator), so the truncation detector uses that
boundary even though configured logical maxima may be higher.

Database `OPEN` requires both `as=<principal>` and `credential=<secret>`.
`CapabilityTable.register_authenticated` refuses empty credentials, and
`authenticate_principal` hashes the candidate and compares all 64 digest
characters; missing, wrong, and unknown credentials use the exact stable
`ERR code=auth msg=authentication failed` response and must not echo or log secrets. All later operations are
session-scoped and deny by default unless the captured capability explicitly
grants the table/access pair.

The established commit order is precheck, capture undo state, apply in memory,
persist with `save()`, then acknowledge. The implementation now uses a
sequential capacity-one mutation owner, persists row-version fields and commit
receipts in the same atomic save, and bounds batch/range requests and responses.
These claims remain implementation-handoff status until focused scenarios
execute on an admitted Stage-4 CLI.

The concrete DB surface includes `DbServerCapsule`, `DbTransport`,
`DbListener`, `TcpDbTransport`, `TcpDbListener`, `DbListenerControl`,
`DbStopControl`, `AuthenticatedPrincipal`,
`CommitIdentity`, and `BoundedQuery`. Production and scripted drains share
`bounded_message_response`, so neither structurally bypasses the final encoded
response-byte check; runtime TCP proof remains uncredited.

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

Temporary staged-binary probe (2026-08-14):

- Path: `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple`
- SHA-256: `5883722a6cafd17006ecab001e714e9e43774014bf44b1af459a92bd142099f5`
- Version: `simple-bootstrap 1.0.0-beta`
- Provenance: `build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-command.transcript`
  records an LLVM `native-build` of `src/app/cli/bootstrap_main.spl` with
  `SIMPLE_NO_STUB_FALLBACK=1`.
- Unverified operator observation: the one HTTP `check` attempt and one focused
  web `test` attempt each
  returned `error: unknown command`; this bootstrap-stage command surface is
  healthy enough to identify itself but is not an admitted verification CLI.
  No acceptance criterion is credited and the deployed failing wrapper was not
  re-probed.
- Unverified operator observation from the final bounded native route: one
  `native-build` used the transcript's
  `x86_64-unknown-linux-gnu`, LLVM, `core-c-bootstrap`, compiler/app/lib source,
  entry-closure, two-thread, dynload, runtime-authority, bootstrap, and
  no-stub-fallback settings with entry
  `test/03_system/web/server/secure_pure_simple_web_server_spec.spl` and output
  `build/verify/secure-pure-simple-web-native/secure_pure_simple_web_server_spec`.
  It exited 1 before linking: HIR could not infer the `ANY` field `error?` in
  the focused spec. No executable was produced, so the conditional execution
  step did not run. Per the single-route constraint, no flag variant or retry
  was attempted and no runtime acceptance is credited.

```sh
env SIMPLE_BOOTSTRAP=1 SIMPLE_NO_DEPRECATED_WARNINGS=1 SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NO_STUB_FALLBACK=1 timeout 300 build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build --target x86_64-unknown-linux-gnu --backend llvm --runtime-bundle core-c-bootstrap --source src/compiler --source src/app --source src/lib --entry-closure --threads 2 --cache-dir build/verify/secure-pure-simple-web-native/cache --mode dynload --entry test/03_system/web/server/secure_pure_simple_web_server_spec.spl --runtime-path build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority -o build/verify/secure-pure-simple-web-native/secure_pure_simple_web_server_spec
```

Observed result (no retained immutable command receipt): exit 1,
`hir: Unsupported feature: cannot infer field type while
lowering main: struct 'ANY' field 'error?'`.

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
