# ASCII split reciprocal allocation and time profile

Executable: `test/01_unit/lib/common/string_core_ascii_split_profile_spec.spl`.

Warm the native implementation, then run 16 splits each on 8 KiB and 32 KiB
records. Each input has a long ASCII field, a UTF-8 field, and a trailing empty
field. Construct inputs before timing and verify all three output fields.

Read the production heap registry around each split. A split must allocate
between 1 and 12 objects, independent of record length. Ending the transient
scope must leave at most two new registry objects. The former slice-per-byte
implementation exceeds this allocation budget by thousands of objects.

Print nanoseconds and total allocated objects. Four times the bytes must stay
below 12 times the smaller duration plus 100 ms, and below 10 seconds in total.
Both measured clocks and allocation counts must be positive; absent counters
cannot produce a passing profile.

Native execution is pending because this host currently lacks a qualified
native SSpec runner. Limits are authored regression guards, not empirical
baseline claims. This unit profile does not replace canonical Stage 3 RSS or
compiler-throughput evidence.
