# HIR re-export diagnostic resource profile

Source: `test/05_perf/compiler/hir_reexport_diagnostic_resource_spec.spl`.

The profile exercises the exact renderer used for a failed facade re-export
chase. With diagnostics disabled, 10,000 and 20,000 misses must render zero
bytes, retain no more than eight live heap objects, scale within 3x plus a
20 ms noise allowance, and complete the larger case within one second.

An explicitly enabled 2,000-miss run is the negative control. It must render
more than 500,000 bytes and allocate more than 1,000 live objects, proving the
profile can detect accidental restoration of unconditional detailed receipts.

This bounded profile prevents memory and performance regressions in the
corrected owner. It does not certify the full jobs=8 Stage 3 RSS budget.
