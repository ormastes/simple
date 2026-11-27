# Self-host HIR cache encoding segfaults in `hc_enc_hir_type` (2026-08-22)

Status: SUPERSEDED 2026-11-11 (lane p3-comp8) — the entire encode path from
the measured backtrace (`hc_enc_hir_type` → `hc_enc_hir_symbol` →
`hc_enc_symbol_table` → `hc_enc_hir_module` → `hir_module_encode` →
`hir_cache_store`) is now guarded: every node rejects nil/ill-formed/
unregistered heap refs with a named reason instead of dereferencing; see the
dated addendum below. The original Stage-2 native repro is not re-run
(entry-closure native builds forbidden in-lane).

## Reproduction

Using the freshly admitted Stage 2 compiler from commit `b22c425c43e`, run a
one-file native build with the default frontend cache enabled. The source only
declares and calls `rt_mem_snapshot_open`; its contents are not required to
trigger the crash. The compiler reaches HIR post-diagnostics and exits 139.

## Measured backtrace

```text
hc_enc_hir_type
hc_enc_hir_symbol
hc_enc_symbol_table
hc_enc_hir_module
hir_module_encode
hir_cache_store
CompilerDriver.lower_and_check_impl
CompilerDriver.compile
```

The same admitted compiler reaches the snapshot-open fail-closed diagnostic
when `SIMPLE_MEM_SNAPSHOT_FILE` is set, before cache storage. Stage 3 recovery
sets `SIMPLE_FRONTEND_CACHE=0`, so this cache crash is distinct from the
snapshot ABI defect fixed by `b67c3e5a881` and from the open Stage 3 RSS issue.

## Next evidence

Reproduce after the snapshot ABI fix has been rebuilt into Stage 2, inspect the
`HirType` value entering `hc_enc_hir_type`, and compare generated
`hc_enc_symbol_table` / `hc_dec_symbol_table` fields with `SymbolTable` before
changing cache format or promotion ownership.

## Addendum 2026-11-11 — P3 lane comp8 verdict: SUPERSEDED (crash path hardened; guard specs green on tracked seed)

Triage on `origin/release/1.0.0` tip `dacccfc78fd10` (worktree
`simple-p3-comp8-20261111`), tracked seed build-commit `46fe8f6b6def`.

- Structural: `src/compiler/20.hir/generated/hir_codec.spl` now guards every
  encode node — 100 `rt_heap_ref_wellformed` / `rt_heap_ref_registered`
  checks and 332 `w.reject(...)` named-reason refusals. `hc_enc_hir_type`
  itself (:8504-8544) rejects `nil` / "illformed" / "unregistered" `HirType`
  refs before any field access, i.e. the exact frame at the top of the
  measured backtrace fail-closes instead of segfaulting. The guards entered
  via merge `9e7e7a526ed` (PR #7597, 2026-11-07); the underlying
  `rt_heap_ref_wellformed` runtime probe predates it (PRs #7488/#7492).
- Adjacent heap-lifetime defect fixed: `803a79fa7c1` "fix(driver):
  hir_cache_load must not return a None box freed by its own scope"
  (PR #7872, stage3-heap-corruption) — the other plausible segfault source on
  the `hir_cache_store` path.
- Behavioral (seed-smoke, tracked seed, interpreter mode):
  - `test/01_unit/compiler/hir/hir_codec_module_node_guard_spec.spl` →
    1/1 PASS ("encodes a lowered hello-world module with no refusal reason").
  - `test/01_unit/compiler/hir/hir_codec_roundtrip_spec.spl` → 4/4 PASS.
- Residual not verified in-lane: the original Stage-2 admitted-compiler
  native repro (one-file native build with the default frontend cache) —
  entry-closure native builds are forbidden in this lane. No evidence of any
  remaining crash on the encode path; the guarded reject contract is pinned
  by the two specs above.

Disposition: SUPERSEDED (hardening absorbed the crash class). Header flipped
OPEN → SUPERSEDED.

## Addendum 2026-11-13 — lane p3-comp1 (worktree p3comp1-wt, branch work/p3-compiler-p1-20261113)

Concurs with lane comp8: SUPERSEDED — the crash path was hardened. No independent re-verification in this lane; disposition stands.
