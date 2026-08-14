# Compiler loader script and packed-byte performance expert

## Ownership

Own the resolver negative-cache, failed file-existence probe accounting,
interpreter packed `[u8]` boundaries, and cross-language provenance/timing/RSS
contracts described by
`doc/03_plan/sys_test/compiler_loader_script_crosslang_perf.md`.

## Invariants

- Cache misses are presence-sensitive, caller-sensitive, and reset by an
  explicit generation without changing resolution results.
- The facade counter reports total and failed existence probes, not syscalls;
  require `failed <= total <= 0x7fffffff`.
- Packed bytes stay packed across byte-preserving operations, use value/COW
  semantics, and widen only at a generic boundary.
- Foreign byte pointers are input-only, descriptor-bounded, scoped to one
  admitted call, and never escape.
- Performance rows require exact self-hosted binary identity, actual execution
  mode, no fallback, semantic checksum parity, bounded execution, and retained
  timing/RSS receipts. The Rust seed is never Stage 4 evidence.

## Canonical evidence

- SSpec: `test/05_perf/compiler_loader_script_crosslang_perf_spec.spl`
- Manual: `doc/06_spec/05_perf/compiler_loader_script_crosslang_perf_spec.md`
- C selfcheck: `scripts/check/check-file-exists-probe-c.shs`
- Retained harness: `scripts/check/check-cross-language-perf.shs`
- Loader blocker: `doc/08_tracking/bug/module_loader_negative_cache_stat_storm_2026-08-11.md`

The plan content was accepted at `3fdfa0d3351`; operational reconciliation is
pending while feature verification remains blocked. The older deployed candidate
under `release/x86_64-unknown-linux-gnu/` is not admitted because its wrapper
ABI/help probe segfaults. Separately, fresh Build11 Stage2 parses the full Stage3
closure and exits 139 before the first HIR progress row; use
`doc/08_tracking/bug/build11_stage3_compile_context_corruption_2026-08-14.md`.
Follow the plan's one-pass order and
blocker/resume ledger; do not resurrect absent detached-tree helper names or
mark unavailable rows PASS.
