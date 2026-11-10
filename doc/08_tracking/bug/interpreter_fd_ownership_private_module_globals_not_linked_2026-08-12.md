# Interpreter does not link FD-ownership private module globals
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** SUPERSEDED — 2026-11-11 (lane interp8): round-8 fix (1889cc95543d) verified live on the fresh seed (build 46fe8f6b6def); `fd_ownership_spec.spl` is 3/3 under `--mode=interpreter`. The 2026-11-10 LIVE reading on the interp3 worktree was stale-binary build skew.
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


## 2026-11-06 round 8: FIXED
Root cause: a module-level `var t: [T; N]` with no initializer was never bound, so the module's own functions failed with "variable not found". `register_definitions` now zero-fills it as a `FixedSizeArray`, and module-global index assignment accepts `FixedSizeArray`. Spec: test/01_unit/os/sosix/fd_ownership_spec.spl (3/3, was 0/3) plus test/01_unit/compiler/interpreter/local_shadows_module_global_spec.spl.


## 2026-11-11 triage — SUPERSEDED (seed-smoke, lane interp8)

Re-ran the record's safe-resume test on the fresh worktree seed
(build-commit `46fe8f6b6def`, `SIMPLE_LIB=src`):
`bin/simple.exe test test/01_unit/os/sosix/fd_ownership_spec.spl --mode=interpreter --no-cache`
-> 3 total, 3 passed, 0 failed, with no `variable ... not found` diagnostic.
The private module-global `[bool; 64]` state links correctly and the
generation/transfer lifecycle assertions pass.

Confirms the round-8 fix (`1889cc95543d` "interp: round 8 fixes (part A)")
is carried by the current deployed seed — the 2026-11-10 LIVE reading on the
interp3 worktree was the stale-binary build skew diagnosed by the same-day
seedfix lane. The companion round-8 spec
`test/01_unit/compiler/interpreter/local_shadows_module_global_spec.spl` is
2/2 on the same binary (see the local_shadows record's 2026-11-11 addendum).
