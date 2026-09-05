# Database request-port evidence authenticity and owner gap

Status: open. The `db-server-request-port` must-check row remains `TODO`.

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

