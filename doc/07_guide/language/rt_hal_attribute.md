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
