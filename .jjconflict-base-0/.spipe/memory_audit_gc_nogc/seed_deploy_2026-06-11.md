# Seed Rebuild + Bootstrap + Deploy — 2026-06-11

Run: `setsid timeout 3600 sh scripts/bootstrap/bootstrap-from-scratch.sh --deploy` (log: /tmp/bootstrap_deploy_2026-06-11.log)

## Stage results
- Stage 1 (Rust seed cargo release build): OK — cranelift backend (LLVM 18 absent). Fresh seed: src/compiler_rust/target/release/simple (54MB, 01:52).
- Stage 2 (seed → stage2 native build): OK.
- Stage 3 (stage2 self-host): FAILED exit 1 — known limitation LIM-010 (LLVM symbol conflicts; see doc/09_report/bootstrap_crash_report_2026_04_01.md). Script fell back to seed for stage 4.
- Stage 4 (full CLI main.spl compiled by seed): built + script DEPLOYED it to bin/release/x86_64-unknown-linux-gnu/simple.
- Stage 5 (MCP servers): built + deployed (simple_mcp_server, simple_lsp_mcp_server) — note: same seed-compiled class as stage4 binary; MCP wrappers run from .spl by default so not hot-path.

## Post-deploy verification → stage4 binary BROKEN, manually replaced with fresh seed
Stage4 CLI (14MB) failed verification: `-c "print(1+1)"` exit 1 no output; `bin/simple test` silent no-op (no Passed/Failed); `bin/simple lint` dumped core on violation AND clean files.

Action: atomically deployed the fresh Rust seed (src/compiler_rust/target/release/simple → bin/release/x86_64-unknown-linux-gnu/simple). Backup of prior seed: bin/release/x86_64-unknown-linux-gnu/simple.bak-2026-06-11 (30MB, Jun 10 — pre-alias-port).

## Final verification (fresh seed deployed)
- `bin/simple -c "print(1+1)"` → 2, exit 0 (setsid+timeout guarded; no process-count runaway, baseline ~7)
- `bin/simple --version` → Simple Language v1.0.0-beta
- Alias lint LIVE: `@no_gc` file + `use std.gpu.*` → `error: runtime family 'nogc_sync_mut' must not import 'std.gpu' (nogc_imports_gc_family) [L:gc_boundary_crossing]`; clean file → OK
- gc_boundary_check_spec: Failed: 0 (13 tests); alloc_checker_spec: Failed: 0 (28 tests)

## Follow-up
- bootstrap-from-scratch.sh --deploy deploys the stage4 CLI without a smoke gate — it shipped a binary whose lint coredumps. The script should run a -c/lint/test smoke before replacing bin/release and fall back to the seed binary on failure. Record as todo/bug if recurring.
- Note: a parallel session is working on a stage3 segfault fix (commit "docs(bootstrap): add stage3-segfault-fix completion report"); coordinate before next bootstrap run.
