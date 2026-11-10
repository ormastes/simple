# Database request-port evidence authenticity and owner gap

Status: open — LIVE owner gap re-confirmed 2026-11-11 (lane ne5); see dated addendum at end. The `db-server-request-port` must-check row remains `TODO`.

A proposed semantic receipt was rejected because the producer accepted
arbitrary server/client binaries and merely hashed their self-authored logs.
A coordinated fake pair could own a listener while fabricating query/result
files without transferring those bytes over TCP. PID-only cleanup also missed
descendants, and no canonical clean-HEAD source-to-Stage4-to-executable chain
was established.

There is currently no declared canonical `src/app/database_server/main.spl`
entry. Plausible existing production owners include
`src/app/postgres_mimic_server/main.spl` and `src/app/redis_server/main.spl`;
the database/server owner must select the gate's protocol and entry before a
production producer can be admitted. A synthetic new path must not be invented
inside the evidence checker.

The next versioned contract must preserve legacy v1 receipt parsing and require:

- the selected committed entry and query fixture, a clean Git source closure,
  retained canonical Stage-4 compiler/provenance, closed build recipe, version,
  and executable hashes;
- exact server-received query and client-received result/status bytes;
- kernel-observed accept/read/write evidence bound to the server-owned socket
  and PID, rather than producer counters;
- monotonic readiness/request/result and stop-only timing;
- process-group/descendant cleanup plus absence of the listener after bounded
  stop; and
- a fresh repository-contained, non-symlink output directory and an unsigned
  reviewer-ready bundle authenticated before attachments are loaded/executed.

Direct database function calls and producer-authored logs are not wire-server
evidence. No proposed v2 importer or validator should land until its matching
producer and real mutation fixtures are coherent together.


## 2026-11-11 addendum (lane ne5)

**Status: LIVE — the authenticity contract was written but the canonical entry
was never established; owner gap persists. Keep OPEN.**

Triage on release/1.0.0 tip:

- The v2 checker `scripts/check/check-db-server-request-port-evidence.shs`
  (landed in PR #7597, hir-nominal-generic-owner-20261107) DOES encode this
  doc's "next versioned contract" requirements: clean-committed source closure
  with repo fingerprint, declared `entry_path src/app/database_server/main.spl`,
  pinned query fixture path, Stage-4 compiler + provenance hashes, kernel-observed
  accept/read/write bound to the server-owned socket and PID, monotonic
  readiness/request/result/stop timing with a stop budget, process-group /
  descendant cleanup with `listener_absent_after_stop`, byte-exact wire hashes,
  and `direct_function_simulation=false`.
- BUT the pinned canonical entry `src/app/database_server/main.spl` does NOT
  exist in-tree, the pinned query fixture
  `test/fixtures/database/server/request_port_query.bin` does NOT exist, and
  the only in-tree producer (`produce-db-server-request-port-evidence.shs`)
  still emits `session/v1` with caller-supplied arbitrary server/client
  binaries — it cannot satisfy its own v2 checker, and no v2 producer exists.
- The must-check ledger row remains `todo, never` with owner
  `server-performance-team` (`doc/08_tracking/check/must_check_db.sdn`).

So the requirement "the database/server owner must select the gate's protocol
and entry before a production producer can be admitted" is still unmet: the
checker hard-codes an entry nobody created. Per this doc's own rule, a
synthetic path must not be invented inside the evidence checker, so NO code
change was made here.

DOC-MISSING: no doc records the entry/protocol selection decision (the
checker hard-codes it; `must_check_db.sdn` still says todo). Grant: the
database/server owner selects or authors the canonical entry
(`src/app/database_server/main.spl` or an existing owner such as
`postgres_mimic_server`/`redis_server`, explicitly), authors the matching
query fixture and the v2 producer, records the selection in the must-check
tiering documentation, and lands producer + checker + fixtures coherently;
then this row can be re-judged.
