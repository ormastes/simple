# 2026-10-31 release/1.0.0 sweep — environmental and harness failure classes (census)

Date: 2026-10-31
Lane: 237-spec sweep (smux unit/system, caret unit/system, smoke) with the
freshly rebuilt Rust seed (`build/sweep-seed-simple-v2`, matches source at
e0a16c5c669). Results TSVs: `build/sweep/results/*.tsv`; per-spec logs:
`build/sweep/logs/`.

Purpose: one index of the failure classes that are NOT product/compiler
defects, so later lanes don't re-triage them. Real defects found in the same
sweep have their own bug docs (linked below).

## Classes

### E1. Windows-only specs run ungated on Linux hosts
~10 smux system specs spawn ConPTY/`powershell.exe`/`cmd` or assert windows
platform strings and fail on Linux (`spawn failed: powershell.exe`,
`expected posix to equal windows`, `FAIL:Windows host required`). The spec
headers describe Windows hosts as the intended lane; no gate skips them on
Linux. Examples: coremux_capture_native, smux_session_lifecycle,
smux_pane_lifecycle (partial), smux_interactive_windows_input (54s),
smux_zoom (partial).
**Workaround tag:** run these on a Windows lane; on Linux treat as
environmental. Owner: smux system-spec lane.

### E2. Specs that spawn `bin/simple` as a child fail on hosts without a deployed CLI
workspace_cli_system (4/4), workspace_recovery (1/7), and the caret workbench
e2e/prod seams fail because `bin/simple` does not exist in a bootstrap-only
checkout; spec headers already document this. Disappears once stage4 deploys.
**Workaround tag:** blocked on stage-4 deploy; do not count as regressions.

### E3. Missing live-service prerequisites
caret_slang_local_hello (no local GGUF model root), infra_servers (SMTP/IMAP,
minio, FTP extern, Confluence) self-mark `BLOCKED:` and the runner maps the
all-pending summary to FAIL. Environmental by design.
**Workaround tag:** gated by `LLM_CARET_*_LIVE=1` + `SLANG_MODEL_ROOT`.

### E4. Smoke specs are self-attesting programs with zero `example()` declarations
All 77 `test/04_smoke/*.spl` report `FAIL ... zero-examples` under
`bin/simple test` even when the program self-passes (42 of 77 print their own
`..._PASS` marker with 0 failures). Harness/spec-convention mismatch, not 77
regressions. Genuine smoke issues found inside the noise: 5 specs still call
deprecated `println` (hard error), `rt_enum_new`/`strlen` unknown externs on
the fresh seed, 8 platform/fixture-gated self-failures.
**Workaround tag:** sweep smoke via `simple run` + self-attestation marker, or
add `example()` wrappers; the println/extern items need their own fixes.

### E5. Host-gated hardware rows
Metal/CUDA/Windows smoke probes fail closed on this Linux aarch64 host by
design (`reason=metal-unavailable`, `FAIL:Windows host required`).

## Real defects triaged from the same sweep (separate bug docs)

- `cross_module_symbol_collision_dispatch_and_sweep_wrong_values_2026-10-31.md` —
  one doc, four causes: (1) PROVEN interpreter last-definition-wins dispatch for
  same-named cross-module functions (minimal repro; pure-Simple inherits the flat
  table at `src/compiler/10.frontend/core/interpreter/eval_tables.spl:279-293`);
  (2) if/match *expressions* revert pending module-global writes in large
  co-compiled units (the remaining `dummy to equal claude_cli` failure at origin
  HEAD; Rust-side machinery cited); (3) vendored stdlib enum collision with no
  warning (enums not covered by the collision census); (4) two stale-spec rows
  since fixed upstream.
- `seed_interp_u8_param_boxed_mux_key_alloc_mismatch_2026-10-31.md` —
  seed interpreter does not coerce `[u8]` literal arguments to declared
  parameters (open gap #4 of `seed_u64_signed_compare_and_u8_data_ptr_2026-10-19.md`);
  explains 16-example `key byte allocation mismatch` cluster + siblings.
- `seed_rt_bytes_to_text_lossy_utf8_split_scalar_2026-10-31.md` — Rust lane
  `[u8] -> text` uses `from_utf8_lossy`; splits a UTF-8 scalar into U+FFFD
  (pure-Simple runtime lanes are byte-preserving).
- `stage2_cache_reuse_hir_ledger_sealed_cache_eacces_2026-10-31.md` — bootstrap
  cache-reuse run cannot create its HIR invocation ledger in the sealed
  published stage2-native-cache.
- `tree_rss_floor_kills_stage2_compiler_tests_on_large_hosts_2026-10-15.md`
  (2026-10-31 recurrence appended, two data points) — phase cap clamps to the
  48 GiB static ceiling; verification matrix exceeds it; only lever below the
  ceiling is fewer build threads + `BOOTSTRAP_VERIFY_TOOL_BUILD_CONCURRENCY=1`.
- sosix capsule surface gap (E1002 on `std.sosix.time`/`stdio` legacy leaves) —
  FIXED concurrently upstream (ffb44049ffd); regression oracle landed via PR #5603.
- 2026-10-31 sweep spec rot (BOM, unterminated `"""`, orphaned `it` blocks)
  — all fixed upstream (ffb44049ffd); caret `413` and `types`/`registry`
  drift — fixed upstream. Verified green at origin HEAD 1dafba57a78.

**Status:** OPEN (tracking census; close classes as their gates land)
