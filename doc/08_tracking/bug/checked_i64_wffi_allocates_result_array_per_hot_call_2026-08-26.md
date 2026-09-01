# Checked i64 WFFI allocates a result array per hot call

- **Status:** OPEN
- **Filed:** 2026-08-26
- **Area:** cached dynamic SFFI call transport
- **Severity:** high — allocation and release occur on every checked call

## Evidence

`spl_wffi_call_i64_checked` represents `[status, value]` as a newly allocated
two-element runtime array in both the native C and Rust providers. The C harness
must explicitly release every result. `DynI64FnSlot.call_checked` uses this API
on the cached hot path, so symbol lookup is avoided but allocation remains.

The new typed boolean thunks do not share this defect: they use scalar status
plus caller-owned output and allocate nothing.

## Unblock condition

Add a cross-lane scalar `spl_wffi_try_call_i64_out` contract accepting the
existing argument array and `*mut i64` output. Initialize output to zero, return
typed bridge status, migrate `DynI64FnSlot.call_checked`, retain the public
`Result<i64, text>`, and benchmark the same cached no-op/zero provider before
and after with allocations, latency distribution, and peak RSS.
