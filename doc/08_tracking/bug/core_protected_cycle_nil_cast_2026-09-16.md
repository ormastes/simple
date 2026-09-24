# core_protected_cycle_spec fails at load: cannot cast nil to i64 (2026-09-16)

## Observed
`bin/simple test test/01_unit/lib/hardware/rv64gc_rtl/core_protected_cycle_spec.spl`
-> outcome=ERROR, zero-examples, `error: semantic: type mismatch: cannot cast
nil to i64` (no file:line). `bin/simple check` passes cleanly on the spec file
and on every imported module (`core_types`, `core`, `core_helpers`,
`protected_core`, `regfile`, `csr`, `mmu_sv39`, `pmp_csr`, `fpu`,
`protected_entry`). Test child binary is
`bin/release/aarch64-unknown-linux-gnu/simple` (seed).

## Impact
1 spec unrunnable; the protected RV64 core cycle coverage it carries is dark.

## Expectation
Spec and all imports pass static check yet the test-runtime semantic phase
rejects a nil->i64 cast; the cast site must be located (likely an i64-typed
field/call resolving to nil at runtime on the aarch64 seed child) and either
the spec fixture or the producing function fixed.

## Unblock condition
Reproduce with a location-bearing diagnostic (or correct-arch child binary),
identify the nil-producing expression, fix it.
