# Stage 4 backend environment missing Backend type import

Status: claimed; production repair deferred after focused cap
Severity: P1 focused closure blocker
Owner: pure-Simple compiler backend environment
Fix owner: `codex/stage4-x86-phase4` in `/home/ormastes/dev/pub/simple-stage4-x86-phase4`
Claimed source revision: `6e9300b345a` plus uncommitted backend facade repair

## Exact failure

After the backend type facade stopped exporting competing enum owners, the
focused real `CompilerBackendImpl` SMF route crossed the original collision and
failed in `src/compiler/70.backend/backend/env.spl` with seven instances of:

```text
unresolved type: Backend
```

The attempt exited 1 after 1m18.61s at 2,272,576 KiB max RSS. The full CLI had
masked this missing import through unrelated flat registration.

## Evaluated owner repair

`Backend` is the compatibility alias owned by
`compiler.backend.backend.backend_api`. A temporary named import resolved all
seven environment errors, but expanded the focused closure into
`backend/codegen.spl`, where separately missing JIT instantiator imports then
failed. The unverified environment edit was restored after the third focused
attempt; no facade wildcard, runtime alias, or generated-code fallback remains.

## Required regression evidence

1. Design a bounded legacy backend interface import that resolves
   `EvalContext.backend` and `HirVisitor.backend` without importing an unrelated
   incomplete modern codegen closure.
2. The same fixture retains the backend facade/direct modern type identity
   assertions and existing distinct-enum collision rejection.

## Retained evidence

- `build/focused/stage4-backend-facade/compile-attempt1.log`
