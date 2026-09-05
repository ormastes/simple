# Interpreter does not link FD-ownership private module globals

**Status:** open  
**Date:** 2026-08-12  
**Area:** compiler/interpreter module dependency linking  
**Affected gate:** SOSIX FD ownership generation and transfer lifecycle evidence

## Reproducer

```sh
bin/simple test test/01_unit/os/sosix/fd_ownership_spec.spl --mode=interpreter
```

The focused specification reports three failures. Each fails before its first
ownership assertion with:

```text
semantic: variable `sosix_fd_own_active` not found
```

## Minimal mechanism

`test/01_unit/os/sosix/fd_ownership_spec.spl` imports the explicitly exported
functions from `os.sosix.fd_ownership`. The function bodies are found and
entered, but their private module state is not present in the interpreter
environment. The first access from `sosix_fd_ownership_init` to the private
fixed-size array `sosix_fd_own_active: [bool; 64]` therefore fails semantic
lookup. The same module also owns the parallel state, PID, FD, and generation
arrays, so all ownership operations are blocked by the same missing dependency
link.

Adding an explicit export contract for the public constants and functions did
not change the failure. The arrays intentionally remain private; exposing
mutable ownership state is not an acceptable workaround.

## Acceptance impact

The interpreter cannot execute the focused acceptance evidence for:

- ownership changes only after explicit transfer completion;
- cancellation preserves the original owner; and
- closing and reusing a slot rejects the stale generation.

The implementation contract is therefore not interpreter-verified. This is a
test/compiler blocker, not evidence that those invariants passed.

## Safe resume test

After fixing private module-global dependency linking, run exactly:

```sh
bin/simple test test/01_unit/os/sosix/fd_ownership_spec.spl --mode=interpreter
```

Acceptance requires `3 examples, 0 failures` and no `variable ... not found`
diagnostic. Do not broaden to the SOSIX or whole repository suite until this
single spec passes.
