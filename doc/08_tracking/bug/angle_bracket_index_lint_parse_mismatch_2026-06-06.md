# Angle-Bracket Index Lint Parse Mismatch

Date: 2026-06-06

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Summary

The compiler warning for bracket array indexing says to use angle-bracket
syntax such as `next_depth<cpu>`, but the parser rejects that expression form in
normal boolean conditions.

## Repro

In `src/os/kernel/scheduler/green_carrier.spl`, changing:

```spl
next_depth[cpu] > 0
```

to:

```spl
next_depth<cpu> > 0
```

and running:

```sh
SIMPLE_LIB=/tmp/simple-cooperative-green/src /tmp/simple-cooperative-green/src/compiler_rust/target/debug/simple check src/os/kernel/scheduler/green_carrier.spl test/01_unit/os/kernel/scheduler/green_carrier_spec.spl
```

failed with:

```text
error[E0002]: unexpected token
  expected: expression
  found:    Gt
```

## Impact

Carrier queue code must keep bracket indexing for now even though interpreter
test output emits a deprecation warning. This is a grammar/lint mismatch, not a
green-carrier behavior issue.

## Required Fix

Either make angle-bracket value indexing parse in expression contexts, or update
the warning so it does not recommend syntax that the parser rejects.

## Re-verification / triage (2026-08-09)

Re-ran both halves of the repro against current `bin/simple`
(`bin/release/x86_64-unknown-linux-gnu/simple`, seed):

- `bin/simple check src/os/kernel/scheduler/green_carrier.spl` still emits the
  lint `Use angle brackets: next_depth<...> instead of next_depth[...]` (and
  several sibling identifiers in the same file/other files), confirming the
  warning is still live.
- A minimal file with `next_depth<cpu> > 0` in a boolean condition still fails
  to parse: `error: ... Unexpected token: expected expression, found Gt`.

Both sides of the mismatch still reproduce exactly as documented — not a stale
defect. `/usr/bin/grep -rln "Use angle brackets" src/` finds the message text
only inside `src/compiler_rust/target/**` build artifacts and
`src/compiler_rust/lib/std/src/parser/error_recovery.spl` (also under
`src/compiler_rust/`) — the lint's source of truth lives entirely under the
Rust seed tree.

Per this sweep's scope rules (no edits under `src/compiler_rust/**`), this
defect is left **OPEN / out of scope for this sweep**. No source changes made.
