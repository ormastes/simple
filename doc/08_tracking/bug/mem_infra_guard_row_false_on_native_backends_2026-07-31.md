# `--mem-infra=guard` is a silent no-op on native backends (matrix claims support)

**Date:** 2026-07-31
**Status:** OPEN — capability matrix asserts a capability that does not exist
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
