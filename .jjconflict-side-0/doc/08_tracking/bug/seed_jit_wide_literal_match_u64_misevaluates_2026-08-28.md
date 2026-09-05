# Seed JIT: literal-arm `match` on u64 mis-evaluates in a stdlib module (2026-08-28)

**Status:** OPEN. Workaround shipped (table scan), filed per CLAUDE.md rule
"when a compact expression form fails ... record a concrete bug".

## Symptom
Inside `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl`, a function of
the shape

```simple
fn csr_is_supported(addr: u64) -> bool:
    match addr:
        case 0xF14: true
        case 0x300: true
        ...
        case _: false
```

returned **false for every input** (including exact arm literals) when run
under `bin/simple run` / `simple test` on the Rust seed (binary: f92fa0bb4d5
tree + hal patch, `--features llvm`, 183,650,976 bytes 2026-08-28 09:03).

## What discriminates
- Identical standalone probes PASS: single- and 29-arm matches, hex vs
  decimal literals, docstring variants, half/quarter splits of the same arm
  table — all true (`build/hal_fx/probe_match.spl`, `probe_arms.spl`,
  `probe_arms2.sh/.spl` in the worktree; copies in the session scratchpad
  `hal/evidence/`).
- The same function imported from the stdlib module OR pasted locally into a
  file that imports the module returned false (`probe_sup.spl`,
  `probe_sup2.spl`) — so the trigger involves the module context (this module
  drops to JIT fallback with `jit-fallback ... rt_char_from_code`), not the
  match shape alone.
- Bisection by arm count/position inside the probe file did NOT reproduce;
  half-tables gave position-dependent false (`h1=false h2=true q3=true
  q4=false` in one run) — evaluation is unstable, not a simple wrong-arm.

## Workaround shipped
`csr_is_supported` uses a `[u64]` table + linear scan instead of `match`
(commit-pending hal intrinsics patch). The csr_read/write intrinsic matches
are unaffected in native codegen (objdump shows every arm; see
`hal/impl_B_REPORT.md`), and their host path is shim-gated before the match.

## Repro
```
build/hal_fx/seed_after run build/hal_fx/probe_sup2.spl   # false false ...
build/hal_fx/seed_after run build/hal_fx/probe_arms2.spl  # h1=false q4=false
```
(from the hal impl_B worktree; probes are also in the scratchpad copy).

## Next step
Minimise from `probe_sup2.spl` + the module import; suspect the JIT-fallback
interpreter's u64 literal comparison in imported-module context.
