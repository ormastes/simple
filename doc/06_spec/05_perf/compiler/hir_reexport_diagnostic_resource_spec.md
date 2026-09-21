# HIR re-export diagnostic resource profile

Source: `test/05_perf/compiler/hir_reexport_diagnostic_resource_spec.spl`.

The profile constructs the production `HirLowering` context with the diagnostic
environment unset and calls the actual failed-chase reporting method. Repeated
10,000 and 20,000 miss rows compare that fixed caller with the parent behavior,
which rendered the detailed receipt on every miss. The fixed rows must emit
nothing and retain no more than eight live objects; the parent control must
retain thousands of objects, grow with the repetition count, render more than
5 MiB, and consume more live heap than the fixed row. No environment lookup
occurs inside a measured miss loop.

An explicitly enabled 32-miss production run includes actual stderr emission,
must report all 32 emissions, and must finish within one second. The 20,000
parent-control renderer must finish within five seconds, preserving a bounded
enabled-path timing oracle without flooding test output.

This bounded profile prevents memory and performance regressions in the
corrected owner. It does not certify the full jobs=8 Stage 3 RSS budget.
