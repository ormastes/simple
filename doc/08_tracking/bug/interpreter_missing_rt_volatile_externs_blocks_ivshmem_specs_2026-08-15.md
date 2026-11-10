# Interpreter has no rt_volatile_read/write_* externs — every ivshmem lane untestable under `simple test`
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-15
**Status:** OPEN
**Severity:** P3 — coverage/testability gap: host-gpu ivshmem code paths
cannot be exercised by any spec on the tree-walk interpreter

## Symptom

Any spec that touches an ivshmem/mmio region via `rt_volatile_read_*` /
`rt_volatile_write_*` fails with `semantic: unknown extern function` under
`bin/simple test` (tree-walk interpreter). The symbols exist only in the
JIT/native table (src/compiler_rust/common/src/runtime_symbols.rs:779-786).

Discovered while driving branch coverage of
src/os/compositor/engine2d_wm_frame_executor.spl: a full rt_alloc
mock-ivshmem region + OS-thread mock host was built, but every
`_render_host_gpu` lane is unreachable — capping that module at 62% (23/37
decisions) headless. See
test/01_unit/os/compositor/wm_frame_executor_branch_coverage_spec.spl
docstring for the per-line catalogue.

## Unblock

Register interpreter handlers for the rt_volatile_* family (plain loads/
stores suffice for hosted mock regions), then extend the executor spec's
host-gpu waves.


## Addendum 2026-11-11 (lane interp6) — SUPERSEDED

**Verdict: SUPERSEDED — fixed on origin/release/1.0.0.**

The tree-walk interpreter now registers the complete volatile family:
handlers live in `src/compiler_rust/compiler/src/interpreter_extern/memory.rs`
(`rt_volatile_read_u{8,16,32,64}`, `rt_volatile_write_u{8,16,32,64}` plus
`rt_memory_barrier` / `rt_load_barrier` / `rt_store_barrier`) and are wired
into the interpreter extern table at
`src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2167-2181`, in a
block whose comment cites this bug doc.

Fixing commit: `9e7e7a526edb43ab29171d920449367e5fd48127` (2026-11-07,
squash-merge of PR #7597) — the pickaxe
`git log -S 'insert_simple!("rt_volatile_read_u8"'` names it as the commit
that introduced the registration, and `git show` confirms the mod.rs hunk.

**Seed-smoke verification (refreshed seed, build-commit 0791c2b7f4a7):**
scratch probe `build/p3fix-interp6/rt_volatile_seed_smoke_spec.spl` (build/,
gitignored, never committed) round-trips u8/u16/u32/u64 volatile writes and
reads plus all three barriers over an `rt_alloc`'d region:

```
SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe $PWD/bin/simple.exe test \
  build/p3fix-interp6/rt_volatile_seed_smoke_spec.spl --mode=interpreter --no-cache
SPEC FILE VERDICT ... outcome=OK declared>=1 executed=1 passed=1 failed=0
Results: 1 total, 1 passed, 0 failed
```

Before the fix every one of those calls aborted with
`semantic: unknown extern function`; they now resolve and round-trip.

Residual (not this bug): the executor spec docstring at
`test/01_unit/os/compositor/wm_frame_executor_branch_coverage_spec.spl:28-32`
still lists the host-gpu ivshmem lanes as a headless ceiling and the spec's
host-gpu waves have not been extended — the "Unblock" follow-up work. That is
a spec-extension task; the interpreter extern gap itself is closed.
