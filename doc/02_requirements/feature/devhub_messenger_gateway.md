# DevHub messenger gateway requirements

Consolidated requirements for the DevHub messenger gateway and content
pipeline, merged into the repository from the master planning artifact
`simple_devhub_sqlite_sqlcipher_messenger_master_plan_2026-10-21.md`
(“Simple + DevHub Complete Upgrade: Native SQLite / SQLCipher, Messenger
Gateway, UTF-8 Codecs, and HTML/ThML → Markdown”). Requirement IDs below
follow the master plan's traceability scheme (section 15) so the executable
SSpecs and future release evidence can bind to them without renumbering.

Scope: a read-only, permission-scoped DevHub gateway over messenger-owned
SQLite/SQLCipher databases and official messenger APIs, plus two reusable
pure-Simple content plugins (`encoding.to_utf8`, `markup.to_markdown`).
Non-goal: DevHub never writes to a messenger-owned database and never sends
through a DB source; general-purpose owned-database write/export/rekey lives
in the database library, behind separately gated APIs.

- REQ-MSG-001: A transport-neutral `MessengerReadPort` (targets, rooms,
  members, paged history, fetch, optional delta) with truthful capability
  levels (`NotImplemented`, `Supported`, `TestedAgainstReference`,
  `LiveVerified`, `ReadOnly`, `WriteEnabled`). Unsupported operations return
  `CapabilityUnavailable`, never a successful-looking placeholder.
- REQ-MSG-002: Versioned external schema mapping (`room`, `room_member`,
  `messages` + provider profile). Identifiers are allowlisted validated
  identifiers, values are bound parameters, `ORDER BY` prefers existing
  indexes, and DevHub never adds indexes or runs DDL on the source DB.
- REQ-MSG-003: Read-only SQLite/SQLCipher messenger DB ingress. The source
  opens through an OS read-only handle with symlink/path-escape rejection;
  `DbAccess::ReadOnly` is enforced at the storage capability layer so even a
  mistaken SQL statement cannot acquire write authority. Live reads require a
  consistent WAL/file snapshot or fail with `SnapshotUnavailable`.
- REQ-MSG-004: Mattermost is the first official API connector (list rooms,
  paged history, membership read, authorized send with receipt). Live
  behavior is verified against a sandbox with real credentials or reported
  `NOT RUN` — mock or outbox-prepared requests are never claimed as delivery.
- REQ-MSG-005: Sending is explicit, gated, and auditable: separate send
  permission, target/room allowlists, user confirmation, stable idempotency
  keys, and delivery states (`Draft`, `UserConfirmed`, `Queued`,
  `Transmitted`, `ProviderAccepted`, `Delivered`, `Failed`, `Unknown`).
  A DB-only target cannot send.
- REQ-ENC-001: Korean decoding: CP949 / Windows-949 / UHC and strict EUC-KR
  to UTF-8, with exact byte-offset diagnostics for malformed sequences. Web
  label `euc-kr` (extended mapping) and strict EUC-KR are distinct named
  modes; strict mode rejects bytes outside KS X 1001.
- REQ-ENC-002: International legacy codecs: Shift_JIS/Windows-31J, EUC-JP,
  ISO-2022-JP, GB18030, GBK, Big5, Windows-1252/1251/1250/1254/1256, KOI8-R,
  ISO-8859 family, anchored in the WHATWG Encoding label/mapping tables.
- REQ-ENC-003: Incremental decoder contract (`begin`/`feed`/`finish`) that
  survives arbitrary chunk splits (including mid-multibyte-sequence and EOF),
  with `strict` / `replace` / `report_and_keep_original` error modes. Unknown
  encoding labels are errors, never silent UTF-8 fallback.
- REQ-MD-001: Pure-Simple HTML → CommonMark/GFM conversion through a
  semantic Markdown IR (Turndown-like ordered rules, keep/remove, contextual
  escaping). Output is semantically validated against reference converters;
  unsafe URL schemes (`javascript:`, `data:`, `file:`) never become active
  links.
- REQ-MD-002: Advanced constructs: nested lists, GFM tables with
  rowspan/colspan loss reporting, fenced code with delimiter selection,
  task lists, strikethrough, entities (full WHATWG table, context-correct
  legacy no-semicolon handling). Unrepresentable content produces an explicit
  `loss_report`, never silent flattening in `faithful` mode.
- REQ-MD-003: Safe ThML profile (`input_kind: thml`) via an explicit
  parser/profile with external entities and DTD expansion disabled; unknown
  tags retain visible text. Malformed/adversarial markup is bounded (depth,
  nodes, attributes, output size, entity expansion) and never executes
  network, filesystem, script, or CSS activity.
- REQ-PLUG-001: `encoding.to_utf8` and `markup.to_markdown` are two
  independently registered pure-Simple content plugins with versioned
  manifests (`encoding.plugin.v1`, `markup.plugin.v1`), static registration
  on constrained targets, and lazy loading for optional providers. Both
  perform real work at release — no blank registries or skeletons.
- REQ-CONFIG-001: Typed `messenger.sdn` target configuration with precedence
  `explicit --target > DEVHUB_MESSENGER_TARGET > .spipe/config.sdn alias >
  user default`. The typed parser rejects unknown keys, duplicate security
  fields, oversized values, invalid identifiers, and missing required
  fields. Repository-tracked SDN can name a target but can never grant read,
  send, path, or credential authority.
- REQ-DEVHUB-001: DevHub CLI verbs (`messenger targets|doctor|capabilities|
  rooms|members|history|search|sync|send|status`, `content decode|convert`)
  route through one shared policy layer; existing DevHub facades and startup
  are unaffected when the messenger lane is unused.
- REQ-SEC-001: Release-blocking security invariants: page HMAC verified
  before plaintext release; constant-time MAC compare; 256000-iteration
  PBKDF2-HMAC-SHA512 with no downgrade path; CSPRNG salt/IV; secrets only
  through `SecretRef` (never argv/SDN/logs); source DB and WAL digests
  unchanged by the source adapter; agent body access denied by default.
- REQ-PERF-001: No DevHub startup regression when the messenger lane is
  unused (lazy provider loading). SQLite/SQLCipher hot paths run compiled
  native/SMF; the 256k KDF runs once per keyed session. Performance claims
  require measured p50/p95/RSS evidence against pinned baselines, recorded as
  `NOT RUN` when missing.
