# Stage-3 callable dependency named/glob precedence (2026-08-21)

## Status

Pure-Simple fix and regressions implemented; fresh bootstrap verification is
pending.

## Exact reproducer

The receipt-bound Stage-3 command recorded in
`build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage3-command.transcript`
completed all 954 streaming surfaces, then first failed while importing
`HirStmtKind` with:

```text
unresolved type: FrontendAsmTargetSpec
```

The previous run with the original field spelling had instead failed with
`ambiguous explicit callable dependency AsmTargetSpec in
compiler.hir.hir_definitions`.

## Root cause

`hir_definitions.spl` intentionally has both a broad `hir_types.*` route and a
direct named route to the three frontend ASM types. Callable signature
dependency materialization treated a differing glob candidate and named
candidate as peers. Aliasing the named imports avoided that diagnostic, but
the downstream staged projection did not preserve the alias spelling, causing
the first error above and a broad imported-type cascade.

## Fix

Retain the declaration's real type names. Explicit named routes now take
precedence over overlapping glob routes; multiple named routes or multiple
glob routes at the same precedence must still agree or fail as ambiguous.
Behavioral coverage imports a callable whose signature type exists behind both
a conflicting glob and an explicit named route. Adjacent source-contract
coverage retains the same-precedence ambiguity diagnostic.

## Verification

Run one fresh Stage-2 admission, produce a new planner admission receipt, and
run one receipt-bound Stage-3/4 deploy. The first HIR diagnostic must be absent;
only a full Stage-4 result can unblock bootstrap must-check evidence.
