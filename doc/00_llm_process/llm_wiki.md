# LLM Repository Wiki

Short, canonical term resolution for coding agents. Read this index when a user
names a repository capability whose implementation owner is ambiguous.

## Simple embedded DB / Simple SQLite

- **Canonical meaning:** `std.database.pure_sql.{PureDatabase}`.
- **Implementation:** `src/lib/nogc_sync_mut/database/pure_sql/`.
- **Nature:** SQLite-compatible DDL/DML/query/transaction engine implemented in
  Simple, with memory and disk-backed operation.
- **Use for:** application-owned embedded SQL persistence that must remain pure
  Simple and work without the C SQLite library.
- **Do not substitute:** `app.io.sqlite_sffi`, `std.io.sqlite_sffi`, or another
  `sqlite_*` SFFI facade; those call C SQLite.
- **Do not confuse with:** `std.database.core.SdnDatabase`, the SDN table/row
  persistence layer rather than the SQLite-compatible SQL engine.
- **Primary guide:** `doc/07_guide/lib/database/sqlite_counterparts.md`.
- **Expert note:** `doc/00_llm_process/feature_expert/database_sql/skill.md`.

### Agent lookup rule

When a request says “Simple embedded DB,” “SQLite in Simple,” or “Simple
SQLite,” search `PureDatabase` and `pure_sql` first. Only choose an SFFI SQLite
surface when the user explicitly requests the host C SQLite implementation.

### Execution rule

The caller's mode does not choose the database execution mode. In normal use,
including an interpreter-hosted CLI, MCP, test harness, or plugin, run
PureDatabase through a cached `.smf`/`.lsm` artifact or native database worker.
Direct interpretation of the database hot path is an explicit diagnostic
fallback only. A carrier *plan* or readiness probe is not proof of offloading;
verify that the caller actually crosses the worker/library boundary.

## Maintenance

Add a compact entry here when repeated ambiguity causes an agent to choose the
wrong repository subsystem. Link detailed guides instead of duplicating them.

## SimpleOS I/O and audio

- **Canonical event owner:** `std.common.io.simple_device_event`.
- **Audio contracts:** `std.common.engine.audio.simple_audio_*`.
- **Guest drivers:** `os.drivers.virtio.virtio_input_*`,
  `os.drivers.virtio.virtio_snd_*`, and the retained x86 HDA service.
- **Hosted event backends:** GLFW and SDL3 are distinct dynamic adapters; one
  must never silently substitute for the other.
- **CUDA audio:** the guest submits bounded Q15 work through a second QEMU
  `ivshmem-plain` device to the pure-Simple host daemon. This is host-driver
  offload, not an in-guest CUDA runtime claim.
- **Two-wire rule:** render/host-GPU owns ivshmem ordinal `0`; audio owns ordinal
  `1`. A first-match or shared mapper aliases the protocols and is invalid.
- **Primary guide:** `doc/07_guide/platform/simpleos/io_audio.md`.

### Verification rule

Run `test/03_system/io_audio/simple_audio_qemu_transport_contract_spec.spl`
after changing PCI/ivshmem ownership. A source check or QEMU preflight does not
replace a live device-origin readback receipt. Non-native platform rows must
report unavailable or pending, never fabricated PASS.

## PostgreSQL mimic / Simple DB server

- **Protocol/session owner:** `std.database.postgres_mimic`.
- **Execution engine:** `std.database.pure_sql.PureDatabase`.
- **Compatibility claim:** PostgreSQL-like startup, session, simple-query,
  transaction-status, row-set, command, and error semantics; do not claim full
  PostgreSQL wire or SQL parity without corresponding contract evidence.
- **Production execution:** cached `build/database/postgres_mimic_server.smf`,
  `.lsm` library, or native executable. An interpreter-mode caller should use
  that compiled artifact rather than interpreting the database hot path.

## LLM Caret messaging

- **Bounded context:** `src/app/llm_caret/messaging/`.
- **Authoritative semantics:** the primitive Simple room; external transports
  publish capability levels and use primitive sidecars for missing behavior.
- **Database:** `std.database.pure_sql.PureDatabase`, never C `sqlite_sffi`.
- **Compiled carriers:** `messaging/{mcp,hook,bridge,database}_worker.spl`; an
  interpreter-hosted launcher still selects a fresh SMF/native worker.
- **Plugin:** `plugins/llm_caret_messaging/` packages Claude, Codex, Gemini,
  MCP, skills, migrations, and guarded ownership metadata.
- **Entry guide:** `doc/07_guide/app/llm/llm_caret_messaging.md`.
- **Evidence:** `doc/09_report/llm_caret_messaging_traceability.md` and
  `.spipe/llm-caret-messaging/state.md`.
- **Development fallback:** direct source/interpreter mode must be explicit and
  is not production evidence.
### Database lookup and execution rule

For database work, search `src/lib/std/database/` first. `PureDatabase` in
`std.database.pure_sql` is the SQLite-compatible implementation rewritten in
Simple; `sqlite_sffi` is the foreign C wrapper. Prefer `PureDatabase`, but run
production hot paths in a cached SMF library or native executable even when the
top-level tool is launched in interpreter mode. LLM Caret's server, MCP, hook,
bridge, and database workers are examples of this carrier pattern.
