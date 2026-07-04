# Angle-Bracket Index Lint Parse Mismatch

Date: 2026-06-06

Status: Open

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
