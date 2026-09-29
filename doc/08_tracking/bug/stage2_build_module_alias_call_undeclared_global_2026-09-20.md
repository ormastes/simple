# Stage 2 build fails: `use M as alias` + `alias.fn(...)` lowers to a load of an undeclared global

- **Filed:** 2026-09-20
- **Status:** WORKED AROUND at the one call site; the lowering defect is OPEN.
- **Severity:** blocked every receipt-free Stage 2 build at `origin/main` `0c25d5eef60`.
- **Found by:** lane `work/stage2-nil-guard-miscompile` (Linux aarch64).

## Symptom

```
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 \
   --mode=dynload --no-mcp --jobs=6 --output=build/bootstrap-nil1
...
FAILED FILES (1):
  - src/compiler/70.backend/backend/llvm_native_link.spl => ... llvm codegen: semantic:
    llvm global load referenced undeclared symbol `llvm_native_link_orchestrator`
VERDICT — ABORTED: stage=stage2 exit=1
```

The seed-built phase-1 compiler compiles `bootstrap_main.spl` into Stage 2 and
fails on exactly one file.

## Trigger

`1df509a0ce5` (2026-09-18) changed `llvm_native_link.spl` from
`use ...llvm_native_link_orchestrator.{link_llvm_native}` to a module alias,
because the file now defines its own `link_llvm_native` wrapper:

```simple
use compiler.backend.backend.llvm_native_link_orchestrator as llvm_native_link_orchestrator
...
    llvm_native_link_orchestrator.link_llvm_native(user_objects, output, options)
```

The pure-Simple lowering running inside the phase-1 compiler treats
`llvm_native_link_orchestrator` as a value (a global) rather than resolving
`alias.fn` to the module function, so the backend emits a load of a global that
was never declared. It is the only `use <module> as <alias>` in
`src/compiler/**` besides `90.tools/verify/checker.spl`, which is not in the
Stage 2 closure.

## Workaround (this lane)

A renamed item import, already used in the tree (`compile_options_hash.spl`,
`smf_hooks.spl`, `swa_zip.spl`):

```simple
use compiler.backend.backend.llvm_native_link_orchestrator.{link_llvm_native as orchestrator_link_llvm_native}
...
    orchestrator_link_llvm_native(user_objects, output, options)
```

With it, the same bootstrap command reaches `Stage 2 admitted; stopping before
Stage 3 as requested.` (EXIT=0).

## Open

The module-alias call form itself still is not lowered by the pure-Simple
compiler. Not reduced to a standalone program in this lane; the next step is a
two-module fixture (`use a as m` / `m.f()`) built with a phase-1 compiler.
