# Retained primary inspection observation age

AUTHORED_NOT_RUN. Three source scenarios exercise the exact production predicate:

1. Retain a real monotonic sample and model cleanup completing beyond the maximum freshness window.
2. Check the installed bound and fixed one-second ceiling in the same nanosecond domain.
3. Refuse unavailable/regressed clocks and nonpositive installed bounds.

Production captures `time_sample_monotonic_nanos_or_failure` before admitting the
actual inspect command, retains it in canonical progress, and transfers that
same bound through the one-use completion claim. The adapter checks the same
clock domain at marker consumption. It never replaces the bound with cleanup
completion/publication time. The delayed completion fixture is modeled arithmetic
around a real clock sample; actual Windows cleanup delay, clock/provider ABI,
marker native mint/use and latency remain NOT_COVERED and NOT_RUN. No docgen run.
