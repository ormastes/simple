# `--mem-infra=guard` is a silent no-op on native backends (matrix claims support)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-07-31
**Status:** SUPERSEDED (native false-claim fixed-at-tip 2026-08-05; re-verified 2026-11-11, lane p3-compiler4)
**Severity:** High for its class. Not a crash; a *false safety claim*. A user who
enables `guard` to hunt a use-after-free on a native build gets no detection and
no warning, and may conclude the UAF is absent.

## Claim vs reality

`src/lib/common/mem_infra/config.spl:34`:

```
MemInfraRow(name: "guard", interpreter: true, cranelift: true, llvm: true),
```

`guard` is a row distinct from `harden`. Enabling it exports
`SIMPLE_MEM_GUARD_RATE=64` (`config.spl:146`); `harden` exports
`SIMPLE_MEM_HARDEN=1` (`config.spl:143`).

**MEASURED 2026-07-31** — readers of each env var, whole `src/` tree:

| env var | C runtime (`src/runtime/*.c`) | Rust `interpreter_extern/` |
|---|---|---|
| `SIMPLE_MEM_HARDEN` | **yes** — `runtime_memory.c` | yes |
| `SIMPLE_MEM_GUARD_RATE` | **NO READERS AT ALL** | yes (`mem_guard.rs:30,176`) |

The `harden` row is the control, and it behaves as the matrix says. `guard` does
not. This asymmetry is the evidence: it is not that the grep was mis-scoped.

Corroborating, in `src/runtime/runtime_memory.c`:
- `rt_mem_guard_stats()` (line 253) is `return 0;` — a stub.
- `grep -c 'mmap\|mprotect'` → **0**. There is no guard-page mechanism in C at all.

## Why native backends are affected

`rt_alloc` has separate implementations per execution model:
- interpreter → `interpreter_extern/memory.rs:589`, wired to the real
  `mem_guard.rs` (`mmap` + `mprotect(PROT_NONE)`, right-aligned overflow,
  delayed `munmap` ring). Genuinely works.
- native (cranelift **and** llvm) → C `rt_alloc` (`runtime_memory.c:257`,
  `runtime_native.c:3805`). No guard pages.

So `guard` is honest only for `interpreter: true`. `cranelift: true` and
`llvm: true` are both false.

`mem_infra_auto_rows()` (`config.spl:44-46`) puts `guard` in the `auto`
expansion for *every* backend, so plain `--mem-infra=auto` on a native build
silently advertises guard coverage it does not have.

## Two candidate fixes — NOT applied, needs a decision

1. **Make the matrix honest** (small, verifiable today): set
   `guard` to `cranelift: false, llvm: false`. The existing degrade machinery
   then reports it, exactly as `asan`/`strict`/`memprof` already degrade. Requires
   updating `test/01_unit/lib/mem_infra/config_spec.spl:33` ("expands auto on
   cranelift to attr, guard, genarena"), and picking a degrade target —
   `harden` is the obvious analog since it is real in C. **This changes
   user-visible behaviour**, which is why it is not applied unilaterally here.
2. **Implement it** — mirror `mem_guard.rs` in `runtime_memory.c`. Closes the gap
   rather than narrowing the claim, but **cannot be verified** until the pending
   bootstrap redeploy lands (see the stage-3 whole-tree parse blocker).

Until one lands, the matrix overstates native coverage.

## Related

- `doc/07_guide/language/dict_native_pitfalls.md` — same family: a native-only
  silent no-op that reads as success.
- Feature acceptance bullet "`--mem-infra=guard` catches a seeded UAF under both
  cranelift-native and interpreter" cannot pass today; it fails on the cranelift
  half for this reason.
- No `test/03_system/runtime/memory_analysis/*.spl` seeded-fault spec exists for
  any model, so nothing currently catches this end-to-end. Existing specs assert
  counters and bookkeeping, not a triggered-and-caught fault.


## Triage 2026-11-11 (p3-compiler4 lane, batch 4 row 4) — SUPERSEDED (native false-claim fixed-at-tip)

At this lane's base:

- This record's candidate fix 1 (honest matrix) is applied:
  `config.spl` row is `MemInfraRow(name: "guard", interpreter: true,
  cranelift: false, llvm: false)`; explicit `guard` on a native backend errors
  ("no fallback") instead of silently degrading; `auto` on cranelift/llvm no
  longer exports `SIMPLE_MEM_GUARD_RATE` (pinned by config_spec, which passes
  12/13 — the 1 RED scenario is the documented policy-kept stale expectation
  per its own NOTE and the spec header).
- Candidate fix 2 (implementation) also landed in source 2026-08-05:
  `src/runtime/runtime_memory_guard.h` wired into `rt_alloc`/`rt_free` in both
  `runtime_memory.c` and `runtime_native.c`, sabotage-verified via
  `src/runtime/test/rt_mem_guard_native_selfcheck.c`. The row stays false
  until a redeployed binary exists, deliberately.
- Environment note: `guard_backend_parity_spec.spl`'s two dynamic arms are
  Unix-only by design — `mem_guard.rs:258-274` documents
  `guard_alloc_sampled` returning `None` on non-Unix ("sampling is simply
  always a miss there... a Unix-only opt-in debugging aid", a 2026-08-09
  decision to unblock the Windows seed link). On this Windows worktree both
  dynamic arms fail by environment; the static arms pass. Not a regression.

No code change in this lane.
