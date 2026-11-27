# Fixed cgroup2 counter parsing

Source: `test/01_unit/lib/common/contracts/container/linux_cgroup_stats_v1_spec.spl`.
Status: **AUTHORED_NOT_RUN**; manually authored, docgen not executed.

The cases call the actual production parser and portable metric validators.
They do not manufacture native owners, admission grants or observed processes.

1. Preserve actual zero, wide positive values and signed i64 maximum. Reject
   signs, negative values, leading zeros, fractions, units, whitespace variants,
   non-ASCII digits, NUL and malformed newline framing.
2. Reject values above i64 maximum before digit multiplication/addition wraps.
3. Read actual cumulative CPU `usage_usec` while validating bounded other fields.
   Keep observed zero distinct from a genuinely absent usage field, represented
   by the fixed explicit unsupported code. Reject duplicate keys, bad framing,
   malformed/overflowing extra fields, more than 64 fields and overlong sources.
4. Aggregate four required I/O counters from distinct valid major/minor device
   records regardless of field order. A genuinely empty source represents an
   observed empty collection. An unavailable source is never fed into that case
   by the native reader and is represented separately.
5. Reject duplicate devices/fields, missing counters, noncanonical device IDs,
   bad numeric values, truncated records, individual and aggregate overflow,
   more than 128 devices, and source data over 32,768 bytes.
6. Validate that unsupported states cannot hide permission errors and that an
   empty I/O device collection cannot claim nonzero traffic.

All 14 cases remain NOT_RUN. Parser acceptance is only DATA validation. Actual
retained container-root identity, provider context, fixed-child native reading,
cleanup, common API integration and runtime behavior require separate complete
path source review and genuine native fixtures; these unit cases qualify none
of those properties.
