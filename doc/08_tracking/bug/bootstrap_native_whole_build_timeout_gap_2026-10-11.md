# Stage2/Stage3 whole-build timeout was not forwarded

The shared command owner passed the RSS cap and sample interval to the canonical
process-tree watchdog but omitted its existing `--timeout-seconds` option. Thus
the native compiler's per-file `--timeout 1800` and the separate sanity-probe
timeout did not bound an entire Stage2/Stage3 native build. The live recovery
source0e0287094ba demonstrated this: Job50216 received timeout0 while enforcing
6291456KiB at100ms. This is not evidence of an RSS containment failure.

The shared owner now forwards `SIMPLE_BOOTSTRAP_NATIVE_BUILD_TIMEOUT_SECONDS`
to the existing watchdog on both Windows and POSIX. Unset preserves its existing
zero/no-deadline behavior; the repair successor launcher explicitly selects7200
seconds. The watchdog validates the value and records its actual timeout in the
receipt. Its Windows Job already terminates the complete workload on timeout.

The active source/cache was not changed or restarted. Its compile completed
successfully in597.0s; admission remains separate. Validation for this plumbing
change is shell syntax plus review of both command paths. No native compiler
qualification is claimed by this change alone.
