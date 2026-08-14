# Feature Expert: enterprise_suite

## Role

Own process knowledge for the Simple Enterprise Suite build-out: the
assessment-driven plan, the shared hardened HTTP core, the durable
enterprise store, and the goods-sale proving vertical. Lane state:
`.spipe/simple_enterprise_suite/state.md`.

## Feature Links

- Research/assessment (authoritative plan):
  `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`
  (linked from `doc/01_research/local/simple_erp.md`)
- Guides: `doc/07_guide/lib/networking/http_server_hardening.md` (+_tldr),
  `doc/07_guide/lib/database/enterprise_store.md` (+_tldr)
- Source:
  - `src/lib/common/net/http_core.spl` — shared protocol core (limits,
    body_decision, bounded chunked decode, path_is_safe, route matching)
    consumed by BOTH `nogc_sync_mut/http_server` and
    `nogc_async_mut/http_server`
  - `src/lib/nogc_sync_mut/enterprise_store/` — durable store (migrations,
    UoW, idempotency, outbox, sha256 audit chain) + `nogc_async_mut` wrapper
  - `src/lib/nogc_sync_mut/enterprise_sale/` — frozen foundation contracts +
    goods-sale vertical (guarded orders, stock ledger, balanced journal)
- Specs (evidence):
  - `test/01_unit/lib/common/net/http_core_spec.spl` (23)
  - `test/01_unit/lib/nogc_async_mut/http_server/async_{parser_limits,path_safety,dynamic_dispatch}_spec.spl` (18/8/6)
  - `test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_spec.spl` (10)
  - `test/03_system/app/enterprise/goods_sale_vertical_spec.spl` (7)
- Prototype being superseded: `examples/12_business/simple_erp/` (in-memory)
  and the split repo `ormastes/simple-erp`

## Constraints and known blockers

- **Interpreter rt_sqlite is a NON-ACID emulation** (transactions no-op,
  constraints unenforced, WHERE-equality ignored, UPDATE unsupported,
  per-path in-process db cache):
  `doc/08_tracking/bug/interpreter_sqlite_externs_nonacid_emulation_2026-08-14.md`.
  The store probes rollback honesty at open (`store_backend_acid`); ACID
  evidence requires native/real SQLite. Store design: insert-only tables,
  pure-Simple tenant filtering, prepared binds, one db path per spec case.
- **Evidence runner caveat:** current spec evidence ran on
  `bin/release/aarch64-apple-darwin/simple` (prints seed banner on some
  commands); the macho-dir deploy is bootstrap-only (no `test`). Re-verify on
  a fresh stage4 self-hosted deploy before verify PASS.
- Edge posture: no direct public TLS/HTTP2 from Simple servers yet —
  edge-proxy deployment per assessment §3.2.
- `std.http.headers` aliased import (`index_of as common_index_of`) is
  unresolvable on the deployed interpreter — http_core carries its own
  bounded chunked decoder instead.

## Verification commands

```bash
bin/simple test test/01_unit/lib/common/net/http_core_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_parser_limits_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_path_safety_spec.spl
bin/simple test test/01_unit/lib/nogc_async_mut/http_server/async_dynamic_dispatch_spec.spl
bin/simple test test/01_unit/lib/nogc_sync_mut/enterprise_store/enterprise_store_spec.spl
bin/simple test test/03_system/app/enterprise/goods_sale_vertical_spec.spl
```

## Handoff notes (2026-08-14)

Waves A (HTTP harden, AC-1..4), B (durable store, AC-5..7), and C slice 1
(contracts + goods-sale vertical, AC-8a/9/10) landed with green specs on the
diagnostic runner. Open: AC-8b rewiring of the example ERP lanes onto
`std.enterprise_{store,sale}` + its ubs_test suite; live-socket dynamic
dispatch system spec; unify `std.http.{limits,path_security}` tier copies
onto http_core; native-mode ACID re-verification.
