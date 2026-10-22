# DevHub messenger SDN and API design

Detail design for REQ-CONFIG-001, REQ-DEVHUB-001, REQ-MSG-002, REQ-MSG-005,
and the `content` plugin facade. Architecture:
`doc/04_architecture/app/devhub/messenger_gateway.md`.

## 1. Typed `messenger.sdn` parser

`config.spl` gains a sibling `messenger/config.spl` with a NEW typed
parser/validator — the legacy `parse_sdn_sections` first-colon/dotted-section
grammar is reused only for lexing. The typed parser:

- rejects unknown keys, duplicate security fields, oversized values, invalid
  identifiers, and missing required fields (never silent coercion);
- enforces the locked `sqlcipher4_4k_sha512` profile values exactly
  (4096 pages, PBKDF2-HMAC-SHA512 256000, HMAC-SHA512, 80 reserved bytes,
  little-endian page-number HMAC, 0 plaintext header bytes); divergence is a
  parse error, not a weaker guess;
- parses into a typed `MessengerTarget` tree (read provider, send provider,
  policy, schema profile, content pipeline, cache mode);
- never returns secrets: `secret_ref` values stay opaque identifiers resolved
  at open/send time by the secret provider.

Precedence: `explicit --target > DEVHUB_MESSENGER_TARGET >
.spipe/config.sdn target alias > messenger.sdn default_target > ERROR`.
Target selection and capability authorization are separate checks: session or
repo config may name a target but can never widen permissions.

## 2. CLI grammar and exit codes

Verbs (REQ-DEVHUB-001): `targets`, `doctor`, `capabilities`, `rooms`,
`members`, `history`, `search`, `sync`, `send`, `status`, plus `content
decode|convert`. Machine-stable output carries `target`, `action`, `source`,
`capability`, `status`, `cursor`, `warnings`, and an optional evidence
receipt. Exit-code convention: `0` success, `1` operational failure, `2`
usage/config, `3` permission denied, `4` unsupported capability, `5`
integrity/cipher failure, `6` partial result — implemented as structured
error codes first so a numeric transition cannot break existing `0/1`
scripts.

`send` requires `--confirm`, a send-enabled API target, and an allowlisted
room; the confirmation re-checks policy at dispatch time against the exact
target/room/body digest. A DB-only target refuses send as a policy error.

## 3. Read contracts

`history`/`search` use keyset pagination (`(seq, id)` tie-breaker) with
default limit 200; `OFFSET` scans on large histories are rejected by the
query planner. Membership visibility is profile-defined (join/leave
timestamps, historical visibility), never a hard-coded rule. Edits/deletes
require delta reconciliation or overlapping checkpoints, not naive
`seq > last_seq`.

## 4. Content facade

`content decode --from cp949 --to utf8 --input FILE` and `content convert
--from html --to gfm --input FILE` are thin facades over the two content
plugins with the pipeline diagnostics (effective charset, error offsets,
loss report, transform versions) printed alongside the output. Binary data
flows via `--input`/`--output` files or stdin/stdout — never via argv.

## 5. GUI / MCP integration

The existing read-only dashboard gains target status, room list, thread
view, search, Markdown preview, and charset/loss indicators; any new
privileged route keeps the loopback-only listener with explicit auth/CSRF.
Sending, where supported, is a separate explicit user action — a read-only
GUI renders drafts without a send button. MCP tool names and argument shapes
mirror the CLI verbs and re-run the same policy layer per call.

## 6. Test obligations

- Unit: typed SDN parser accept/reject tables; precedence chain; policy
  matrix; capability levels.
- Integration: read-only fixture DBs (plain + SQLCipher synthetic fixtures),
  schema-profile mapping, keyset pagination, WAL snapshot failure mode.
- System: `test/03_system/app/devhub/feature/messenger_gateway_spec.spl`
  end-to-end scenarios (doctor/rooms/history/send-denied) once the lane
  lands; generated manual under `doc/06_spec/03_system/...` (`.md` only).
- Performance: no-regression startup/RSS for unchanged facades.
