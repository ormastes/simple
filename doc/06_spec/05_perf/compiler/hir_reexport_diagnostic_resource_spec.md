# HIR re-export diagnostic resource profile

Source: `test/05_perf/compiler/hir_reexport_diagnostic_resource_spec.spl`.

The profile constructs the production `HirLowering` context with the diagnostic
environment unset and calls the actual failed-chase reporting method. The
parent control renders the same detailed receipt and consumes it through an
injectable sink, preserving its formatting and allocation cost without
flooding stderr. Three 20,000-miss trials provide median elapsed, allocation,
and live-heap values. The fixed median must retain no more than eight live
objects, remain within the parent median plus 20 ms, scale within 3x plus 20 ms
from the 10,000 row, and complete within one second.

Three explicitly enabled 8-miss production trials include actual stderr
emission. Their median must finish within one second and all 24 calls must
report emission. The parent-control median must finish within five seconds.
The incoming environment is restored before profiles and assertions run.

This bounded profile prevents memory and performance regressions in the
corrected owner. It does not certify the full jobs=8 Stage 3 RSS budget.
