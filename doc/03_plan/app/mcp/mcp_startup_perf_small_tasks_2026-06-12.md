# MCP Startup Perf — Small-Task Plan (2026-06-12)

Research: `doc/01_research/app/mcp/mcp_startup_handshake_perf_2026-06-12.md`.
Goal: default MCP startup → tens of ms (LSP-MCP shape); keep 151-tool surface opt-in.

Model levels: **haiku** = mechanical/measurement, **sonnet** = scoped implementation,
**opus** = cross-cutting architecture/design.

## Lane A — Measurement (parallel-safe, read-only + this file)

- [ ] A1 (haiku): run `sh scripts/check/check-mcp-native-smoke.shs`; record elapsed for
      full MCP and LSP MCP under "Baseline" below.
- [ ] A2 (sonnet): `bin/simple deps fast|normal|deep src/app/mcp/main.spl` (+
      `SIMPLE_LOADER_TRACE=1` / `SIMPLE_PROFILE=1` variants); record closure size, top
      exclusive-cost imports, hub `export use *` offenders.
- [ ] A3 (sonnet): split timings start→initialize, start→tools/list, start→first
      tools/call; record which phase dominates.

## Lane B — Server (`src/app/mcp/**` only)

- [ ] B1 (sonnet): add `--probe` CLI flag to `main.spl`: prints version, build id, tool
      count, tool-manifest hash; exits 0. No MCP framing, no handler imports.
- [ ] B2 (sonnet): make first `tools/list` cheap — cache-once stays, but build the
      response as a single literal/precomputed table instead of repeated string concat
      via `_mcp_static_tools_result()` schema generation.
- [ ] B3 (opus): cut top-level handler imports from `main.spl` / `main_dispatch.spl`
      startup path; dispatcher table tool_name → handler module, loaded on first
      `tools/call`. Startup path = stdio framing + initialize + manifest only.
- [ ] B4 (opus, later): `tool_set = core|all` config split (core ~15–25 tools default,
      full opt-in); optional `tools/list` pagination.

## Lane C — Wrapper/scripts (`scripts/setup/setup.shs`, wrapper templates only)

- [ ] C1 (sonnet): wrapper probe uses `candidate --probe` when supported (fallback to the
      existing full-handshake grep when `--probe` unsupported) — removes one full server
      boot from cold/stale starts.
- [ ] C2 (haiku): keep full handshake probe in CI smoke
      (`scripts/check/check-mcp-native-smoke.shs`) — verify unchanged, no sleeps.
- [ ] C3 (haiku): note in docs: never benchmark via
      `test/03_system/tools/mcp/mcp_startup_test_system.shs` (sleep 1 × 3) or via npx.

## Lane D — Dependency cut (`src/lib/nogc_sync_mut/mcp_sdk/**` only)

- [ ] D1 (sonnet): `bin/simple deps` over mcp_sdk; identify hub modules / `export use *`
      pulling wide closures into the server boot path.
- [ ] D2 (sonnet): narrow imports (symbol-specific `use`), split hub modules where a
      single symbol drags hundreds of files; re-measure closure delta.

## Sequencing

A, B, C, D run in parallel (disjoint file scopes). C1 lands with handshake fallback so it
does not depend on B1 being deployed. B3/B4 are the big wins but riskiest; B1/B2/C1 are
quick wins. Re-run Lane A after each lane lands.

## Baseline (filled by Lane A)

Measured 2026-06-12 on Linux x86_64, stage4 self-hosted binary, cache-warm second run.

### A1 — Smoke timing

| Server | startup_ms | notes |
|--------|-----------|-------|
| `bin/simple_mcp_server` (MCP) | **1522** (first run, cache hit) / **1602** (second) | both cached; budget ≤5000 ms ✓ |
| `bin/simple_lsp_mcp_server` (LSP-MCP) | **34** | thin wrapper, no tool-schema work |

- `mcp_probe_cache_hit=true` on first run → probe cache already populated.
- `mcp_second_start_note=both_cached_first_run_already_hit_cache`
- MCP server is ~45× slower than LSP-MCP at startup. Target: bring MCP into LSP-MCP shape.

### A2 — Dependency closure (`src/app/mcp/main.spl`)

| Metric | Value |
|--------|-------|
| Total closure files (deep) | **38** |
| Direct imports from main.spl | **20** |
| Largest transitive import | `main_dispatch.spl` — 22 transitive files |
| mcp_sdk server cluster | `mcp_sdk/server/app.spl` — 9 transitive; **7 exclusive** (highest) |

Top exclusive-cost direct imports (files unique to that import):

| Import | Exclusive | Shared | Notes |
|--------|-----------|--------|-------|
| `mcp_sdk/server/app.spl` | 7 | 2 | largest exclusive block |
| `nogc_sync_mut/io/stderr_ops.spl` | 1 | 0 | small, isolated |
| `mcp/mcp_log_options.spl` | 1 | 0 | small, isolated |
| `mcp/main_lazy_protocol.spl` | 1 | 0 | small, isolated |
| `mcp/main_static_tools.spl` | 1 | 6 | tool_table chain |

Hub / `export use *` offenders in closure:
- `src/app/mcp/assistant/session_store.spl` uses `export use app.mcp.assistant.session_store_helpers.*` / `session_store_part1.*` / `session_store_part2.*` (3 star re-exports). Not in the hot startup path (lazy).
- `mcp_sdk` `__init__.spl` files use explicit symbol lists only — no star exports. Clean.
- `src/lib/sffi/cli.spl:3` has a known `export use *` lint warning (pre-existing, unrelated).

`main_dispatch.spl` imports all 10 lazy handler modules at startup (22 transitive files). This is the primary B3 target for lazy loading.

### A3 — Phase timing

| Phase | ms (median of 3 runs) |
|-------|-----------------------|
| start → `initialize` response | **~1460** |
| `initialize` → `tools/list` response | **~2–3** |
| Total (start → `tools/list`) | **~1463** |

- **start→initialize dominates** (~99.8% of total cost). Tool-schema generation (`tools/list`) is essentially free once the server is loaded.
- The 1460 ms is process startup + module loading + tool-table construction, all before the first JSON-RPC response.
- LSP-MCP at 34 ms shows the achievable floor when handler imports are deferred.

### Profiling update (2026-06-12, native binary — CORRECTS A3)

The wrapper actually execs `build/bootstrap/mcp-package/simple_mcp_server` (2 MB native
ELF, libc-only, stripped), NOT `bin/release/.../simple_mcp_server` (which exits silently
when run directly — separate bug worth checking). Direct phase timing of the packaged
binary:

| Phase | Time |
|-------|------|
| start → `initialize` response | **~0 ms** (262 B, 9 file opens, no .spl/.smf reads) |
| `initialize` → `tools/list` response | **~1.5 s, 100% user CPU**, 11.5 MB RSS |

So in the NATIVE server the cost is entirely **tools/list response construction**, not
module loading (A3's earlier attribution applies to the interpreted path only). gdb
stack samples at 0.4/0.8/1.2 s all land in one function (PC ~0x5dd7ed–0x5dd93f) with
`__memcpy_avx_unaligned_erms` beneath — repeated full-buffer string copying plus a
per-character tight loop: the O(n²) string-concat / char-indexed JSON-escape pattern in
the tools-list builder (and the rt string primitives under it). 38 KB output should cost
~10 ms; it costs 1500 ms.

Implications (no arch/interface change needed):
- A build-time pre-escaped literal manifest (research item 4) reduces tools/list to a
  single write → expected ~1.5 s → tens of ms, byte-identical response.
- The rt-level string hot path (concat realloc-copy, O(i) char_at in escape loops) is a
  general script-perf bug: fixing it speeds up ALL Simple scripts, not just MCP.
- B2's table-driven rewrite must be re-measured natively — it removed duplicate schema
  generation but still string-concatenates; without a parts-array + single join (or the
  literal manifest) it may remain slow.

### Summary for Lane B/D

The bottleneck is entirely in start→initialize: ~1460 ms. Cutting handler imports on the startup path (B3) is the highest-leverage change. `mcp_sdk/server/app.spl` has the largest exclusive closure (7 files) and is a candidate for narrower imports (D1/D2). `main_dispatch.spl` importing all lazy modules eagerly is the structural root cause.
