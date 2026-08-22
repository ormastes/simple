# `@rt(hal)` operations

Declare a runtime/HAL operation on a function with the ordinary attribute:

```simple
@rt(hal, operation: io.read.v1,
    providers: pure+c+rust,
    capabilities: 9,
    comparator: 11,
    normalizer: 12,
    effects: plan_then_commit,
    request_bytes: 256,
    result_bytes: 512)
fn read_operation(value: i64) -> i64:
    value
```

The no-configuration policy is `critical`, all three isolated providers,
Pure Simple preferred, Plan-Then-Commit effects, and fixed capacities. Critical
and Verified operations imply `@no_alloc`, emit a bounded manifest plus one
link marker, and automatically select the sealed HAL archive. Untagged programs
emit neither marker nor manifest and do not link the archive.

`assurance` accepts `moderate`, `strict`, `robust`, `critical`, or `verified`.
Any value below `critical` requires a non-empty `rationale` and is rejected when
the operation is in a Critical entry closure. `providers` uses `pure+c+rust`
syntax; `preferred` must name an admitted provider. Unknown fields, malformed
policies, zero capacity, and values above 4 MiB fail closed.

The remaining optional bounded fields are `trace_operations`, `trace_bytes`,
`diff_rows`, `report_bytes`, `log_bytes`, `deadline_ticks`, `error_schema`, and
`environment_schema`. Runtime configuration cannot widen these compile-time
caps. Provider arrival order never grants commit authority; the parent compares
validated normalized I/O and owns the sole commit.

## Production clock migration

`std.io.time_now_nanos` is the first production I/O wrapper carried by this
contract. Its operation is `io.clock.monotonic_nanos.v1`. It deliberately omits
`assurance`, so the compiler promotes it to Critical and implies `@no_alloc`.
The request, result, and replay trace are fixed scalar envelopes (32 bytes, one
trace operation), and the existing raw clock is called exactly once.

The manifest admits isolated Pure-Simple, C, and Rust lanes. C remains preferred
while the Pure-Simple clock provider is maturing: normal mode runs only C and
preserves the legacy wrapper's latency and return/error behavior; alpha and beta
compare the same capture-once observation through replay lanes. Existing
`current_time_unix`, `current_time_ms`, `time_now_nanos`, and `time_now_micros`
names remain compatible. The bounded migration checker continues to warn for an
exact untouched legacy raw-clock declaration until its release epoch, while a
new or changed untagged declaration is an immediate error.
