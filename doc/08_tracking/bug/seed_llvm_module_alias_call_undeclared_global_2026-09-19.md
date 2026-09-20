# Seed LLVM codegen lowers a module-alias call to an undeclared global

- **Date:** 2026-09-19
- **Status:** SOURCE WORKAROUND LANDED. The seed codegen gap is OPEN.
- **Severity:** P1 (aborts strict Stage 2 on every host)
- **Area:** Rust seed LLVM codegen and name resolution (`src/compiler_rust/compiler`)

## Recorded failure

Commit `1df509a0ce5` (2026-09-18) changed `llvm_native_link.spl` from a
selective import to a whole-module alias, and called through it:

```simple
use compiler.backend.backend.llvm_native_link_orchestrator as llvm_native_link_orchestrator
...
    llvm_native_link_orchestrator.link_llvm_native(user_objects, output, options)
```

Strict Stage 2, which is the seed compiling the bootstrap compiler, then
aborted with:

```text
FAILED FILES (1):
  - src/compiler/70.backend/backend/llvm_native_link.spl: llvm codegen: semantic:
    llvm global load referenced undeclared symbol `llvm_native_link_orchestrator`
```

This was measured in the FreeBSD QEMU lane, but the failure comes from the
seed's shared codegen, not from anything FreeBSD-specific.

## Minimal reproduction

The two-file fixture below was compiled with the same seed binary and the same
`native-build --backend llvm --entry-closure --mode dynload` flags as Stage 2:

| `wrap.spl` form | result |
|---|---|
| `use fx.orch as orch` + `orch.link_it(n)` | `llvm global load referenced undeclared symbol 'orch'` |
| `use fx.orch.{link_it as orch_link_it}` + `orch_link_it(n)` | builds; the binary prints `42` |

## Workaround (landed)

A renamed selective import is the idiom already used across `src/compiler`,
for example `use x.{a as b}`. The contract test
`test/01_unit/scripts/seed_backend_module_alias_contract_test.shs` keeps
whole-module alias imports out of `src/compiler/70.backend`.

## Open: seed fix

The seed should resolve `alias.fn(...)` for a module alias the same way it
resolves a selectively imported `fn`, instead of emitting a global load. Other
whole-module alias imports still exist on `main` outside the Stage 2 failure
path:
- `src/app/init/main.spl`
- `src/app/io/jit_sffi.spl`
- `src/compiler/90.tools/verify/checker.spl`
- the two `game2d/__init__.spl` files

Any of them becomes a Stage 2 blocker if it enters the seed-compiled closure.
