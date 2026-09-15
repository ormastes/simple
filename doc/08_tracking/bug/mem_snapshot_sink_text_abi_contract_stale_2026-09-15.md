# memory_snapshot_sink_source_spec asserts the retired raw-pointer snapshot ABI (2026-09-15)

`test/01_unit/compiler/driver/memory_snapshot_sink_source_spec.spl` asserts the
Stage3 memory-snapshot provider ABI passes raw `(ptr, len)` pairs:

- `extern fn rt_mem_snapshot_open(path_ptr: i64, path_len: i64) -> i64`
- `rt_mem_snapshot_open(rt_string_data(path), rt_string_len(path))`
- and `not_to_contain("rt_mem_snapshot_open(path)")`.

The src moved to text-typed externs:

- `driver_mem_snapshot.spl:9` — `extern fn rt_mem_snapshot_open(path: text) -> i64`
- `driver_log_helpers.spl:12,52` — same text extern, called `rt_mem_snapshot_open(sink)`.
- No `rt_string_data/rt_string_len` marshaling remains in either file.
- Env access changed `rt_env_get("SIMPLE_MEM_SNAPSHOT_FILE")` → `env_get_opt(...) ?? ""`
  (driver_mem_snapshot.spl:55).

The spec's `use std.test.*` import (module does not resolve from stdlib roots)
was fixed to `use std.spec.{describe, it, expect}` in the same pass — the spec
now loads; 4 of 5 examples fail on the ABI-shape assertions.

## Unblock condition

Decide the ABI of record: if text-typed externs are the sanctioned shape, the
spec's raw-ABI assertions (including the `not_to_contain` guard) must be
rewritten to the text contract with equal strength; if raw pairs are required
(e.g. for the memory-snapshot budget discipline the spec describes), the src
regressed. Do not soften to vacuous assertions.
