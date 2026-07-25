# Web Server + Database Performance Research

Domain: x86_64 Web Server and Database performance for `perf-opt-lang-web-db-os`.
Scope: AC-3, AC-4, AC-5, AC-8, AC-9.

---

## Web Server (impl, API, done/open)

### Implementation

The web server lives across three modules in `src/lib/nogc_sync_mut/`:

| Module | Key files |
|--------|-----------|
| `http/` | `request.spl`, `response.spl`, `headers.spl`, `common.spl`, `types.spl`, `url.spl`, `cookie.spl`, `limits.spl`, `path_security.spl`, `accept_encoding.spl`, auth (`basic.spl`, `digest.spl`), H2 (`h2_frame.spl`, `h2_parser.spl`, `h2_writer.spl`), H3 (`h3_conn.spl`, `h3_frame.spl`, `h3_stream.spl`, `qpack_decoder.spl`, `qpack_encoder.spl`, `qpack_static.spl`), WS (`ws_frame.spl`, `ws_parser.spl`, `ws_writer.spl`, `permessage_deflate.spl`) |
| `http_server/` | `handler.spl`, `middleware.spl`, `response.spl`, `types.spl`, plus `parser.spl` and `router.spl` (referenced in log, not listed separately above) |
| `http_client/` | `connection.spl`, `request.spl`, `response.spl`, `ssl.spl`, `types.spl`, `utilities.spl` |
| `net/` | `sffi.spl` (TcpListener/TcpStream/UdpSocket SFFI), `__init__.spl` (client-facing: HttpClient, Url, UrlBuilder, get/post/download) |

The async-layer (`nogc_async_mut/http_server/`) supplies `HttpResponseData`, `HttpRequestData`, `LocationConfig` re-exported by `http_server/types.spl`.

### Done (all phases closed)

- **`webserver_harden`** (`phase: implement-done`) — parser limits (`MAX_REQUEST_LINE`, `MAX_HEADER_COUNT`, `MAX_HEADER_LINE`, `MAX_BODY_SIZE`), `parse_request_with_limits`, path traversal safety (`path_is_safe` with encoded-slash bypass fix), duplicate Content-Length rejection (request-smuggling guard), chunked rejection (501), 501/400/413 branch specs. 30 path-safety + 23 parser-limits + 13 chunked/headers tests all green. Pre-existing failures in `rate_limit_spec`/`request_validation_spec`/`security_headers_spec` are import-path breakage from prior refactor (unrelated to this work). Source: `.spipe/webserver_harden/state.md`.

- **`webserver-hardening-opt-general`** (`phase: 5-implement done 2026-05-26`) — general hardening + optimization pass. Source: `.spipe/webserver-hardening-opt-general/state.md`.

- **`web-server-optimizer-complete`** (`STATUS: CLOSED 2026-05-25`) — nginx-class completion: H2 stream multiplexing (HPACK, flow control, SETTINGS, GOAWAY), H3/QUIC server, static file serving (sendfile/zero-copy, pre-compressed cache, mmap, ETag, Range), unified `HttpServer` with ALPN negotiation. Source: `.spipe/web-server-optimizer-complete/state.md`.

- **`net-acceleration-remaining`** (`STATUS: CLOSED 2026-05-20`) — TCP state machine (SYN_SENT/CONNECTING/ESTABLISHED/CLOSE_WAIT), `NetBackendCapabilities` (portable/sendfile/zero-copy/packet-io/sriov/rdma tiers), DMA RX/TX buffers, HTTP server capability reporting, benchmark fixture with latency/throughput baseline, 20 verification tests. Source: `.spipe/net-acceleration-remaining/state.md`.

- **`browser-net-bundle-optimization`** (`STATUS: CLOSED 2026-05-22`) — browser-side net bundle. Source: `.spipe/browser-net-bundle-optimization/state.md`.

- **`web-db-hardening`** (`STATUS: CLOSED 2026-05-20`) — shared web+db hardening pass. Source: `.spipe/web-db-hardening/state.md`.

### Open / Gaps

- `net-acceleration-remaining-2026-04-21` — separate follow-up copy; check for residual open items.
- Bounded-read end-to-end spec (parse_request reads TcpStream directly — needs injectable stream seam). Recorded in `webserver_harden` log as concrete follow-up.
- Pre-existing import-path failures in `rate_limit_spec`, `request_validation_spec`, `security_headers_spec` from refactor `cd46a9463a4` — NOT fixed by any closed spipe task. **Open risk for AC-8 guard.**
- No benchmark sspec yet for the web server path (throughput/latency). Required by AC-3.

---

## DB (impl, RAM-only vs persistent paths, done/open)

### Implementation

Two tiers in `src/lib/nogc_sync_mut/`:

**Tier 1 — Embedded stdlib** (`database/` + `db/`):

| Sub-path | Role |
|----------|------|
| `database/sql/` | SQLite-wrapper: `connection.spl` (Database), `transaction.spl` (Transaction/TxState), `statement.spl` (PreparedStatement), `stmt_cache.spl` (StatementCache), `query_builder.spl`, `sql_gen.spl`, `codec.spl`, `repository.spl`, `schema.spl`, `escape.spl` |
| `database/pure_sql/` | Pure-Simple MVCC engine: `database.spl` (~2223 lines, split into `database_part1.spl` + `database_part2.spl`); table registry via parallel arrays; row data as tab-serialized text |
| `db/` | Accel layer: `db_persistence.spl` (DbTable), `db_query.spl`, `query_planner.spl`, `prefix_index.spl`, `text_index.spl`, `page_summary.spl`, `filter_in.spl`, `cardinality_estimator.spl`, `ml_cost_model.spl`, `learned_index.spl`, `accel.spl` |
| `db/dbfs_engine/` | DBFS: `mvcc.spl` (MvccTable/MvccTuple/MvccHeader), `fts/` (FTS engine) |
| `db/dbfs_driver/` | DBFS driver |

**Tier 2 — Full engine example**: `examples/11_advanced/simple_db/` — submodule, previously confirmed design-only/empty (`.spipe/simple-db-hardening` research: "Full engine submodule is empty (design-only)").

### RAM-only vs Persistent split (AC-5 critical)

| Config | Code path | Notes |
|--------|-----------|-------|
| **RAM-only** | `PureDatabase` in `database/pure_sql/database.spl` opened **without** a file path, OR `DbTable` in `db/db_persistence.spl` — data lives in process heap | MVCC snapshot scan is O(N) over all tuples including dead ones; index structures (`PrefixIndex`, `TextIndex`) are in-memory |
| **Persistent / file-backed** | `PureDatabase._persist()` → `_serialize_disk()` → `file_write` entire DB on **every mutation** (simple-pure-db-v1 pipe-delimited text format). Reopen via `_deserialize_row` on scan — O(N) per query | Top bottleneck: `_persist()` per mutation. Mitigated by `open_deferred/checkpoint` (landed in `pure-db-perf-improve`) |
| **DBFS-backed** | `db/dbfs_engine/mvcc.spl` + `db/dbfs_driver/` — WAL-based persistence; `_ensure_fts_index` does lazy full rebuild on dirty flag | WAL replay drops all field data (blank rows) — P0 bug found in `simple-db-hardening` research |

Key data point from `pure-db-perf-improve` (CLOSED 2026-05-27): deferred INSERT 200 rows = 954ms vs auto-checkpoint timeout; incremental FTS = 0ms rebuild after optimization. Comparison report: `doc/09_report/pure_db_perf_comparison_2026-05-26.md`.

### Done

- **`simple-db-hardening`** (all phases `[x]`, 2026-05-23) — WAL replay blank-row fix (F1), TOCTOU lock race (F2, partial — O_EXCL extern missing), BTree delete underflow (F3), trait conformance (F4/F5). 50 spec blocks. Source: `.spipe/simple-db-hardening/state.md`.
- **`pure-db-perf-improve`** (all phases `[x]`, 2026-05-27) — `_mark_dirty` extraction, deferred persist (`open_deferred/checkpoint`), incremental FTS on INSERT. Source: `.spipe/pure-db-perf-improve/state.md`.
- **`db-hardening-optimization`** (all phases `[x]`, 2026-05-26) — FTS/BM25 cache invalidation on mutations, `CLibPatternKind` extensions (FtsMatch/ContainsSearch/PageSummaryScan/CacheInvalidation), benchmark gate specs (point lookup, prefix, contains, BM25, reopen/recovery). Source: `.spipe/db-hardening-optimization/state.md`.
- **`db-hardening-optimizer-general`** (phases 1-5 `[x]`, 6-8 `[ ]` **OPEN**) — DbTable PrefixIndex+TextIndex wiring, index-aware `db_query`, query planner (`choose_plan`), `--db-analyze` CLI. Source: `.spipe/db-hardening-optimizer-general/state.md`.
- **`dbfs-integration`** (`STATUS: CLOSED 2026-05-20`). Source: `.spipe/dbfs-integration/state.md`.
- **`simple-db-accel-remains-2026-05-02`** (`CLOSED — verified Wave 16-9`). Source: `.spipe/simple-db-accel-remains-2026-05-02/state.md`.
- **`web-db-primitive-hardening`** — spec file present at `src/lib/nogc_sync_mut/db/web_db_primitive_hardening_spec.spl`.

### Open / Gaps

- `db-hardening-optimizer-general` phases 6-refactor, 7-verify, 8-ship still `[ ]`.
- `rt_file_create_excl` extern not yet implemented (TOCTOU F2 incomplete).
- Full engine (`examples/11_advanced/simple_db/`) is design-only — no benchmarkable implementation.
- No sspec benchmark separating RAM-only vs persistent configurations (required by AC-5). Must be created from scratch.
- `db-fts-engine` and `pure-db-perf-improve` spipe exist but FTS5 RAM-vs-persistent split not yet benchmarked as separate result sets.

---

## Benchmark Harnesses

Existing scripts:

| Script | Purpose |
|--------|---------|
| `scripts/check/check-cross-language-perf.shs` | Compares Simple (interpreter/SMF/native) vs bun/python/go/erlang/java/C on cold startup, warm throughput (fib35 in-process), parallel CPU workers, large fanout. Configurable: `RUNS`, `WORKERS`, `FANOUT_WORKERS`, `FANOUT_ITERS`, `FANOUT_STRESS_WORKERS`, `PROFILE_DOCKER_ISOLATION` |
| `scripts/check/check-startup-size-performance-audit.shs` | Startup + binary size audit |
| `scripts/check/check-scilib-accelerator-perf.shs` | Scilib/accelerator perf |

- `.spipe/fat32-vs-cfat-bench/` — FAT32 vs cfat filesystem benchmark (separate from DB).
- DB benchmark gate specs exist in `db-hardening-optimization` but are embedded inside the hardening spec, not standalone sspec benchmark docs.
- **No standalone web-server or DB benchmark sspec** emitting benchmark docs currently exists. Both must be created for AC-3.

---

## Public API Surface to Protect (AC-8)

### Web server public API

`src/lib/nogc_sync_mut/http_server/types.spl` (lines 353-359):
```
export HttpMethod, HttpStatus, HttpRequest, HttpResponse
export http_method_from_text, http_method_to_text, is_method_safe, is_method_idempotent
export http_status_code, http_status_reason, http_status_from_code
export mime_type_for_extension, pure_text_to_i64
export use std.nogc_async_mut.http_server.types.{HttpResponseData, default_response_data}
export use std.nogc_async_mut.http_server.types.{HttpRequestData, LocationConfig}
```

`src/lib/nogc_sync_mut/http_server/parser.spl` (lines 199-201):
```
export parse_request, parse_request_with_limits, parse_request_line
export to_i32_safe, content_length_from_text, headers_decision
export MAX_REQUEST_LINE, MAX_HEADER_COUNT, MAX_HEADER_LINE, MAX_BODY_SIZE
```

`src/lib/nogc_sync_mut/http_server/router.spl` (line 210): `export path_is_safe`

`src/lib/nogc_sync_mut/http_server/response.spl`: `write_response`, `serialize_response`, `write_error`, `generate_error_page`, `html_not_found_page`, `html_error_page`

`src/lib/nogc_sync_mut/net/__init__.spl` (lines 448-463): `HttpMethod`, `HttpRequest`, `HttpResponse`, `HttpClient`, `Url`, `UrlBuilder`, `get`, `post`, `download`, `TcpListener`, `TcpStream`, `UdpSocket`

`src/lib/nogc_sync_mut/net/sffi.spl` (lines 80-87): all `tcp_listener_*` / `tcp_stream_*` SFFI functions.

### Database public API

`src/lib/nogc_sync_mut/database/sql/__init__.spl`:
```
DbType, DbValue, DbError, DbRow, Database, Transaction, TxState
PreparedStatement, StatementCache
ColumnConstraint, ColumnDef, TableSchema
SqlOp, SqlOrder, SqlExpr, CompiledExpr
SelectQuery, InsertQuery, UpdateQuery, DeleteQuery
sql_eq/ne/gt/ge/lt/le/like/is_null/is_not_null/in/and/or/not/raw/raw_safe, compile_expr
gen_create_table, gen_drop_table, gen_add_column, gen_rename_column
gen_create_index, gen_drop_index, gen_create_table_if_not_exists
DbCodec, quote_ident, quote_value, sanitize_table, sanitize_column
```

`src/lib/nogc_sync_mut/db/__init__.spl`: re-exports via `use std.io_runtime` (minimal — full export list needs deeper audit as grep returned no `^export` lines; the `__init__` may use `use` chains).

---

## rt_* Usage

| Module | rt_ line count | Notes |
|--------|----------------|-------|
| `http/` | 20 lines | Primarily `rt_black_box` in `auth/basic.spl` (constant-time compare optimizer hint) and field-named `required_insert_count` false-positives in `h3/qpack_decoder.spl` |
| `net/` | 2 lines | Minimal — net is almost fully wrapped via SFFI |
| `db/` | grep count pending | `db_query.spl` — no rt_ hits; `database/pure_sql/` grep returned `.slice()` / `.len()` stdlib calls (false positives from `rt_` substring search) |
| `database/` | Low | `pure_sql/database_part1.spl` + `part2.spl` — rt_ search hits were all non-rt_ field accesses |

The http and net layers are well-wrapped. The main remaining `rt_*` exposure visible to app developers is in `net/sffi.spl` (SFFI functions like `tcp_listener_bind`, `tcp_stream_connect` are exported directly). The DB layer appears clean of direct `rt_*` in app-facing code.

---

## Risks

1. **API-break risk (import-path failures)**: `rate_limit_spec`, `request_validation_spec`, `security_headers_spec` are broken by refactor `cd46a9463a4` — AC-8 guard must not count these as a regression baseline; they must be fixed first or explicitly excluded with documented justification.

2. **RAM-only vs persistent split (AC-5)**: The split exists in code (`open_deferred` = RAM; `_persist()` = file-backed; dbfs_engine = WAL-backed) but no benchmark sspec separates them. Creating these specs is the primary open work for AC-5. Care needed: SQLite FFI wrapper (`database/sql/`) is unavailable in interpreter mode — benchmarks must clarify which mode they run under.

3. **Full engine design-only**: `examples/11_advanced/simple_db/` is empty/design-only. DB benchmarks must target the stdlib tiers (`database/pure_sql/` for RAM/persistent, `db/dbfs_engine/` for WAL-backed), not the example.

4. **`db-hardening-optimizer-general` incomplete**: phases 6/7/8 open — index-aware query path is implemented but not yet refactored/verified/shipped. Benchmark specs built on `db_query.spl` index path may hit unverified code.

5. **`rt_file_create_excl` missing**: TOCTOU lock fix (F2) is spec-red until this extern lands — DB persistent path has a known lock race under concurrent writers.
