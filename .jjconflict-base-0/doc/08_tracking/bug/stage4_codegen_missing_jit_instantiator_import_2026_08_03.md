# Stage 4 codegen missing JIT instantiator imports

Status: claimed; no production edit in this focused lane
Severity: P2 isolated closure blocker
Owner: pure-Simple compiler backend codegen facade
Fix owner: unassigned after the backend-facade focused cap
Claimed source revision: `6e9300b345a` plus uncommitted backend facade/env repairs

## Exact failure

The second focused `CompilerBackendImpl` SMF route crossed the backend enum
collision and the named `Backend` environment import, then failed in
`src/compiler/70.backend/codegen.spl` on unresolved `JitInstantiatorConfig` and
`JitInstantiator` names.

The attempt exited 1 after 1m38.81s at 3,496,964 KiB max RSS. The full CLI
closure previously masked these imports through unrelated registrations, so
this is tracked as an isolated-closure robustness defect rather than the next
confirmed full x86 blocker.

## Required follow-up

1. Identify the canonical JIT instantiator owner and add named imports at the
   pure-Simple codegen facade.
2. Add a focused codegen/JIT adjacent regression without relying on flat global
   registration.
3. Do not add runtime aliases or weaken unresolved-name diagnostics.

## Retained evidence

- `build/focused/stage4-backend-facade/compile-attempt2.log`
