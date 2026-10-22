# DevHub messenger gateway architecture

Architecture for REQ-MSG-001..REQ-SEC-001 (see
`doc/02_requirements/feature/devhub_messenger_gateway.md`). Consolidated from
the 2026-10-21 master planning artifact into the repository per the SPipe
doc-layer conventions.

## 1. Process boundaries

```text
devhub messenger CLI / GUI / MCP
        |
  typed messenger.sdn  (user-owned; repo SDN names targets, never grants)
        |
  ReadPort        SendPort (API only)        devhub content CLI/API
     |                 |                            |
 SQLCipher/SQLite   Caret outbox            encoding.to_utf8
 read-only reader   HTTP delivery                |
     |                 |                     markup.to_markdown
 schema mapping      provider ack               |
     +--------+--------+------------------------+
              |  normalized ExternalMessageEnvelopeV1
              v
       Caret canonical domain (reused, not reimplemented)
```

Ownership rules (one owner each):

1. One SQL engine and one storage contract; format providers own pager/pages
   only — never a second query language.
2. One SQLCipher page codec under the database codec owner; DevHub selects a
   DB source but never re-implements AES or page authentication.
3. One charset implementation per codec in the stdlib encoding owner; the
   `encoding.to_utf8` plugin is a registry/streaming adapter, not a fork of
   mapping tables.
4. One HTML tokenizer/entity owner (shared Blink/stdlib); the markup plugin
   supplies conversion rules against one Markdown IR.
5. One canonical messenger domain + outbound worker (Caret); DevHub supplies
   UX, config, read-only readers, and policy.
6. One SDN resolver with separate user-owned targets vs repo-scoped aliases.
7. One plugin admission mechanism (kernel/aspect dynload or static
   registration); lazy optional providers, never a second process loader.

## 2. Component view

| Component | Owns | Consumes |
|---|---|---|
| `src/app/devhub/cmd_messenger.spl` | CLI verbs, output shapes, exit codes | policy, read/send ports |
| `src/app/devhub/messenger/config.spl` | typed `messenger.sdn` parse/validate | SDN lexer conventions |
| `src/app/devhub/messenger/target_resolve.spl` | target precedence chain | config |
| `src/app/devhub/messenger/policy.spl` | read-only enforcement, send grants, agent ACL | capabilities |
| `src/app/devhub/messenger/schema_profile.spl` | allowlisted table/column identifiers, schema fingerprint | DB introspection |
| `src/app/devhub/messenger/query_plan.spl` | fixed prepared queries, keyset pagination | validated identifiers |
| `src/app/devhub/messenger/content_pipeline.spl` | ordered plugin chain + provenance | content plugins |
| `src/app/devhub/messenger/adapter/sqlite_reader.spl` | read-only SQLite ingress | std.database storage port |
| `src/app/devhub/messenger/adapter/sqlcipher_reader.spl` | SQLCipher ingress | codec owner |
| `src/app/devhub/messenger/adapter/mattermost_api.spl` | Mattermost read/send | Caret transport |
| `src/app/llm_caret/messaging/port/read_contracts.spl` | `MessengerReadPortV1`, envelope | domain model |

## 3. Read-only enforcement (not advisory)

- OS-level read-only open of an existing approved path; realpath resolution
  rejects symlink traversal and path escapes; no open mode can create a file.
- `DbAccess::ReadOnly` is enforced at the storage capability layer, so even a
  mistaken SQL statement cannot reach `commit_pages` or a writable descriptor.
- Fixed SELECT-only query templates with bound parameters; allowlisted
  identifiers only; no `ATTACH`, no UDFs, no arbitrary `PRAGMA`.
- Source file/WAL ownership stays with the messenger: no rekey, DDL,
  checkpoint, `VACUUM`, or mark-as-read paths exist in the reader closure.
- Live reads require a stable snapshot (WAL end-mark + file identity) or fail
  with `SnapshotUnavailable`; `immutable=true` only for frozen copies.

## 4. Capability truthfulness

Providers publish capability levels; only the admission process advances the
evidence level. A mock or outbox-prepared send is `Queued`/`Prepared`, never
`Delivered`. Disallowed: claiming live verification from fixtures, claiming
send from a DB-only target, silently coercing unsupported operations.

## 5. Agent (MCP) boundary

MCP tools mirror CLI verbs and re-run the same typed target/policy checks per
call. Message bodies are untrusted user-origin content: delimited, provenance-
bearing, never able to grant tool permissions. Agent access to bodies is off
by default and scoped per target/room/session.

## 6. DevHub non-regression

The messenger lane is lazy: `devhub tasks/git/wiki/storage/email` and
`devhub --help` must not import messenger, SQLCipher, codec, or markup
closures (REQ-PERF-001). Startup/RSS benchmarks for the unchanged facades are
part of the release gate.
