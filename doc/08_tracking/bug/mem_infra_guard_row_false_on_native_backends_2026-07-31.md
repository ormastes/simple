# `--mem-infra=guard` is a silent no-op on native backends (matrix claims support)

**Date:** 2026-07-31
**Status:** RESOLVED 2026-08-02 via option 1 (matrix corrected) — see
"Resolution" at the bottom. The claim now matches measured behaviour; the
underlying *gap* (no guard pages on native) is unchanged and option 2
(implementing them in C) remains open as a separate piece of work.
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
  counters and bookkeeping, not a triggered-and-caught fault. *(Closed by the
  resolution below: `guard_backend_parity_spec.spl` is that seeded-fault spec.)*

## Resolution — 2026-08-02

The 2026-07-31 diagnosis above was static (grep for env-var readers). It has now
been confirmed **behaviourally**, which is the only evidence that settles a
safety claim: `test/fixture/mem_infra/guard_uaf_probe.spl` commits a real
use-after-free in a child process and reports which side of the fault it
reaches. Measured on the Rust **seed** (`bin/simple`; the bootstrap-identity
probe `strings bin/simple | grep -c "enum construction: unregistered enum"`
returns 0, i.e. the Rust driver):

| backend | matrix claimed | `SIMPLE_MEM_GUARD_RATE=1` | knob unset (control) | verdict |
|---|---|---|---|---|
| interpreter | true | **SIGSEGV**, `survived` never printed | survives, exit 0 | claim **TRUE** |
| cranelift | true | survives, exit 0 | survives, exit 0 | claim **FALSE** — knob inert |
| llvm (native-build) | true | survives, exit 0 | survives, exit 0 | claim **FALSE** — knob inert |

Mechanism, traced rather than inferred: cranelift resolves `rt_alloc` through
`RuntimeSymbolProvider`/`dlsym` (`codegen/jit.rs:315`), **not** through the
`interpreter_extern` table where `mem_guard.rs` is wired — so the JIT never
reaches the guard allocator even though both live in the same process. `nm` on
a `native-build` output shows a locally-defined `T rt_alloc` that is a plain
`malloc`. Only the interpreter routes through `interpreter_extern::mem_guard`.

Applied (option 1): `guard` is now `interpreter: true, cranelift: false,
llvm: false`, and `mem_infra_auto_rows` no longer puts `guard` in the `auto`
expansion for cranelift/llvm — that expansion was the mechanism by which plain
`--mem-infra=auto` exported `SIMPLE_MEM_GUARD_RATE=64` on native builds and made
a no-op look enabled.

**`guard` was deliberately given NO degrade target**, contradicting the
suggestion above that "`harden` is the obvious analog since it is real in C".
Two reasons. First, the two are not equivalent: a guard page traps *at* the
faulting access, whereas harden only notices later, when something calls
`rt_mem_harden_check()` — silently swapping one for the other answers "yes, you
have UAF detection" to someone who asked for the trapping kind, which is the
same false-safety failure in a new place. Second, harden's own status on
cranelift is **not established**: running `harden_poison_workload.spl` under
`SIMPLE_EXECUTION_MODE=jit SIMPLE_MEM_HARDEN=1` reported `tampered_check=0`
where the interpreter reports a violation. That may mean the harden row is also
inert on cranelift, or merely that the `rt_mem_harden_check` extern is
interpreter-only; it was not resolved here and is **not** claimed either way.
Worth noting for whoever picks it up: there are two C `rt_alloc` definitions —
`runtime_memory.c:249` (harden-capable) and `runtime_native.c:4517` (plain
`malloc`) — and the native binary binds the latter, which is exactly the
`-z muldefs` first-definition-wins hazard.

Regression cover: `test/01_unit/lib/mem_infra/guard_backend_parity_spec.spl`
asserts each backend's matrix row against its observed trap/no-trap behaviour,
so the row cannot drift back to an unmeasured claim.

**Sabotage-verified.** A spec that passes with and without the protection proves
nothing, so the guard implementation itself was disabled — `guard_free_sampled`'s
`mprotect(..., PROT_NONE)` changed to `PROT_READ|PROT_WRITE` — and the seed
rebuilt. The interpreter example went **red** (`assert_equal failed: expected
false, got true` — the UAF survived) while the other three stayed green; after
reverting and rebuilding, green again on the same binary path.

That cycle also exposed a real defect in the first draft of the spec: it
resolved `SIMPLE_TEST_BINARY` with `env_get` (copied from sibling specs), the
runner does not surface that variable to a spec body, and so **every run
silently used `bin/simple` and ignored the override** — the first sabotage
attempt passed for that reason alone. The override is now expanded by the child
shell (`${SIMPLE_TEST_BINARY:-bin/simple}`) instead. Sibling specs that use the
`env_get` form for the same purpose are likely to have the same dead override.
