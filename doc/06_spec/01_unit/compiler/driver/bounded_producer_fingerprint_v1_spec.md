# Bounded current producer fingerprints

Source: `test/01_unit/compiler/driver/bounded_producer_fingerprint_v1_spec.spl`.

Six native-provider obligations: compare the bounded result against the legacy canonical digest on a regular nested tree; reject a real self-referential symlink before following it; reject oversized bytes before hashing; bound tree depth and complete-directory entry count; detect equal-length source mutation; and stop before reading a second file when file admission is exhausted. Every fixture is private and removed before assertions. The symlink scenario uses the POSIX `ln` utility; unsupported providers must not be counted as positive coverage.

Status: **NOT_RUN** for Simple execution. The separate native directory-owner selfcheck does not qualify these compiler tests. Loaded executable authority additionally requires actual parent launch-pin/control validation; controlled digest inputs only test observed component composition. Performance and atomic filesystem generation remain OPEN.
