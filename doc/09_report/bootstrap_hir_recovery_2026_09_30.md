# Bootstrap HIR recovery implementation review — 2026-09-30

STATUS: WARN — source implementation and review completed; native qualification pending.

Workspace: `D:/wk-bootstrap-keep-going-20260930`, branch
`work/bootstrap-keep-going-20260930`. Changes remain uncommitted. This report
does not qualify a runtime, authorize publication, or report a bootstrap PASS.

## Implemented behavior

- The native parent resolves ordered CLI policy, explicit environment policy,
  and the CI default before spawning workers. Serial builds receive one HIR
  worker unless sharding/cache prerequisites were explicitly disabled.
- Every HIR worker publishes the same frozen source inventory and closure
  identity, then claims each physical source before cache decoding or lowering.
  Worker generations have distinct owner tokens. Claims are immutable and
  terminal writes require the matching owner under the queue lock.
- Module outcomes are PASS, FAILED, CRASH, or BLOCKED. PASS records distinguish
  CACHE_STORED from UNCACHED; these records never authorize cache reuse. Cache
  availability checks decode entries through the existing cache loader, keeping
  producer/source/closure identity checks intact.
- A crashed worker's unfinished claims become terminal CRASH after confirmed
  termination. A replacement can claim only previously unclaimed modules.
  Diagnostic-budget exits can also rotate when they made new claim progress.
  Each replacement consumes previously unseen work; preflight failures with no
  claims become global BLOCKED and cannot create an endless replacement loop.
- Traversal completion requires an explicit worker receipt. After all children
  stop, the coordinator closes unclaimed inventory rows as BLOCKED or SKIPPED
  under fail-fast. Missing/corrupt accounting, incomplete traversal, diagnostics,
  and crashes all prevent the final worker, linking, and artifact publication.
- Successful cache payloads and failure evidence remain on disk for inspection
  and reuse within the existing cache lineage. Recovery does not delete cache
  entries or use terminal records to bypass decoding.

## Independent review corrections

The design reviewer identified and the implementation addressed:

1. Timeout cleanup could seal a claim while its worker still ran. Sealing and
   inventory closure now require confirmed termination. A wait result of `-1`
   is an error, not termination proof; even a false liveness probe is insufficient.
   Kill plus a bounded second wait must yield a real exit result, otherwise the
   invocation remains BLOCKED with the live claim untouched.
2. Unreadable directories and truncated claim/PASS records could look empty.
   Optional directory reads and record validation now fail closed.
3. Substring classification could confuse a filename containing `scope` or
   `ownership` with a guard failure. Classification uses specific diagnostic
   prefixes and the parser's exact guard suffixes.
4. A shard without a valid cache identity could fall through into final build
   phases. Both HIR paths now reject that condition before lowering.
5. Unvisited modules were implicit. Frozen inventory publication and coordinator
   closure now account for them explicitly without taking a live owner's claim.

SCV admission, source identity, memory snapshot, and ownership guard failures
remain BLOCKED. Their checks have not been disabled or retried through bypasses.

## Evidence and limits

`git diff --check` passed for the changed implementation files. The focused
SSpec file is `test/03_system/compiler/driver/hir_shard_recovery_spec.spl` and
exercises production policy/ledger seams, ownership, corruption, replacement,
and inventory outcomes in 32 scenarios. Its execution is pending an admitted
self-hosted runner. The design/policy review lane separately reported a native
smoke PASS for 10 pure policy cases on its first attempt; that evidence does not
execute the worker, filesystem ledger, or HIR pipeline integration.

Worker waits remain sequential. A later worker's failure may therefore be
observed only after an earlier worker exits or reaches its timeout. This is an
existing orchestration limitation; this change does not claim prompt concurrent
failure observation, improved latency, or measured memory savings.

The following checks are UNEXECUTED for this implementation:

- `<admitted-runtime> test test/03_system/compiler/driver/hir_shard_recovery_spec.spl --mode=interpreter`
- `<admitted-runtime> check src/compiler`
- `<admitted-runtime> check src/lib`
- `<admitted-runtime> check src/app/mcp`
- `<admitted-runtime> check src/app/simple_lsp_mcp`
- `SIMPLE_LIB=src <admitted-runtime> test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`
- The required core runtime and MCP native smoke checks, plus any real crash
  injection/bootstrap retry that would establish process-level qualification.

No heavy bootstrap was started in this lane. Earlier SCV publication/memory
tasks remain safety-blocked and outside its scope; no unchanged blocked lane was
retried. Focused seams alone would not establish native bootstrap qualification.
