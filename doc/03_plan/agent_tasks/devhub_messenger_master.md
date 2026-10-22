# DevHub messenger gateway — master implementation plan

Next-step plan per `doc/00_llm_process/pipeline_next_step_plan.md` (lead-agent
format: refined request, selected experts, findings, delegated lanes,
artifacts, verification, knowledge-update targets).

## Refined request

Deliver the DevHub improvement defined by
`doc/02_requirements/feature/devhub_messenger_gateway.md`: a read-only,
permission-scoped messenger gateway over messenger-owned SQLite/SQLCipher
databases and official messenger APIs, plus two reusable pure-Simple content
plugins (`encoding.to_utf8`, `markup.to_markdown`). Security and correctness
outrank speed; every phase ships requirement → SSpec → test → implementation
traceability with truthful evidence (no stub passes, no unrun claims).

## Selected experts

- Feature expert: `doc/00_llm_process/feature_expert/devhub/skill.md`
  (facades, config/auth SDN, gh-shim traps, translation policy).
- Feature expert: `feature_expert/database_sql` (PureDatabase, SQL parser,
  storage formats).
- Feature expert: `feature_expert/caret_workbench` (messaging domain, ports,
  transports, outbox).
- Layer experts: compiler/driver (effective import tier, lazy closure),
  crypto owners (PBKDF2/HMAC/AES reuse rules), encoding owner, markup/HTML
  owner, verification/SSpec owner.
- Stage experts: `pipe/research`, `pipe/design`, `pipe/impl`, `pipe/verify`
  per the runtime process in the Next doc.

## Expert findings (input to lanes)

1. devhub: facades are backend-neutral with one precedence chain
   (`backend_resolve.spl`); the messenger lane must add its own typed SDN +
   policy layer without importing Caret's agent runtime into DevHub startup.
   Keep every pure-translate surface testable offline.
2. database_sql: existing SQL support is NOT on-disk SQLite; a true
   pager/B-tree/record codec is new work. Never reinterpret
   `PureDatabase.open()` as a SQLite opener; new formats enter only through
   format-explicit APIs.
3. caret_workbench: reuse the canonical domain + outbound delivery; add an
   external `MessengerReadPort`. `*_outbox` results mean queued/prepared,
   never delivered.
4. crypto: one HMAC-SHA512 owner; add no-padding CBC page primitives; never
   route 4016-byte pages through PKCS#7 wrappers; audit the exact effective
   import graph (historical alias bugs).
5. verification: fixtures must come from pinned independent reference tools;
   roundtrip-only tests are inadmissible for crypto and format claims.

## Delegated lanes (one file owner per lane)

| Lane | Owner paths | Gate to done |
|---|---|---|
| P0 contracts | `std.database` storage port, `PageCodecV1`, `MessengerReadPortV1`, plugin ABI SDN | specs fail correctly against missing implementation |
| CR-A crypto | `src/lib/common/crypto/**` additions (no-pad CBC), KAT/perf | independent NIST/RFC vectors, native parity |
| DB-A/B SQLite | `database/sqlite_format/**` reader then writer | reference `sqlite3` opens output; `integrity_check=ok` |
| CR-B SQLCipher | `database/codec/sqlcipher4*.spl` | pure↔reference binary read/write both directions; tamper/wrong-key reject |
| MS-A/B messenger | `messenger/port/read_contracts.spl`, DevHub readers | read-only fixture ingress; source digests unchanged |
| ENC-A/B codecs | `common/encoding/**` + plugin adapter | WHATWG corpora, split-byte streaming tests |
| MD-A/B markup | `common/markup/**` + plugin adapter | CommonMark/GFM semantic fixtures; adversarial bounds |
| API-A Mattermost | `adapter/mattermost_api.spl` | sandbox live read/send receipts or `NOT RUN` |
| P8 DevHub UX | `cmd_messenger.spl`, `cmd_content.spl`, policy | existing facades regression-free; scoped denials |
| P9 hardening | fixtures, CI, docs, perf | every release gate green with actual command logs |

Merge strategy: narrow reviewable commits per lane; shared ABI changes need
producer + consumer tests before merge; feature flags keep the lane inert
until admitted.

## Expected artifacts

- Code: paths listed in `doc/04_architecture/app/devhub/messenger_gateway.md`
  §2 (created lane by lane; nothing lands as a skeleton).
- Specs: unit/integration SSpecs per lane; system spec
  `test/03_system/app/devhub/feature/messenger_gateway_spec.spl` at P8.
- Docs: this plan, requirements, architecture, design (landed); generated
  `.md` manuals only under `doc/06_spec/**` (never `.spl` there).
- Evidence: receipts + fixture hashes under `doc/09_report/`; perf under
  `doc/10_metrics/`; bug DB entries for every discovered reproducible
  failure.

## Verification commands

```bash
bin/simple test --no-session-daemon test/01_unit/app/devhub/<spec>.spl
bin/simple test test/01_unit/lib/common/encoding/
bin/simple test test/01_unit/lib/common/markup/
bin/simple test test/01_unit/lib/database/sqlite_format/
bin/simple test test/02_integration/app/devhub/messenger/
sh scripts/audit/direct-env-runtime-guard.shs --working
# release lane additionally: compiler/core/lib checks per AGENTS.md Step 4
```

A check that did not run is `NOT RUN`, never zero or PASS.

## Knowledge-update targets

- `doc/00_llm_process/feature_expert/devhub/skill.md` — add messenger lane
  links + traps after each landed lane.
- `doc/00_llm_process/feature_expert/database_sql/skill.md` — storage format
  selection notes.
- `doc/00_llm_process/feature_expert/caret_workbench/skill.md` —
  `MessengerReadPort` contract and envelope versioning.
- `doc/07_guide/app/devhub.md` — user-facing messenger/content sections at
  P8; `doc/08_tracking/feature/**` typed SDN states per REQ row.
- Refactor checkpoint (per Next doc): after implementation cleanup, scan
  `doc/`, `.claude/skills/`, `.codex/skills/`, `doc/00_llm_process/` for
  stale references and record changed paths in `.spipe/<feature>/state.md`.
