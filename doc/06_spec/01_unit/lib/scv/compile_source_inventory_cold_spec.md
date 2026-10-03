# Cold source inventory replay

Status: **authored companion, unexecuted, not generated** (2026-10-03).
Source: `test/01_unit/lib/scv/compile_source_inventory_cold_spec.spl`.
Nine scenarios exercise the actual cold reducer and compare successful results
against the original per-event reducer's canonical encoding.

| Scenario | Independent oracle |
|---|---|
| Unique mixed-source creates | Reversed Git/filesystem create events starting at generation 41 yield sorted entries, generation 44, both changed flags true, and byte-identical sequential encoding |
| Duplicate creates | Identical create followed by replacement counts two changes, not three; final one-entry encoding agrees with sequential replay |
| Modify/delete fallback | Two creates, one modification and one deletion retain one source, increment generation four times and match sequential encoding |
| Empty/negative initial state | Empty batch preserves generation and false changed flags; negative generation rejects with no partial inventory |
| Maximum valid generation | One create at i64 maximum minus one yields the maximum exactly, matching the serial oracle |
| Churn and no-ops | Existing mixed create/modify/delete/duplicate workload preserves generation and canonical bytes |
| Invalid events | Existing invalid-path, operation, digest and producer fixtures preserve the serial first-error reason and return no partial state |
| Empty/delete-only | Existing empty and missing-delete fixtures leave generation unchanged |
| Sort stability | Existing reverse odd-size/equal-identity fixtures preserve expected source ordering and tie order |

The optimization reuses `compile_source_inventory_initial_events_v1` only for
fully validated unique create batches. It adds the supplied initial generation
without overflow; mixed/duplicate/invalid batches and overflowing offsets keep
the original reducer path. Authority, publication, cache and locking behavior
are unchanged. No event is skipped because the fast path refuses a batch.

This source change removes per-entry singleton inventory/reducer calls in the
common unique-create path. Runtime speedup is unmeasured, and the historical
360-second diagnostic timeout is not attributed to this overhead. Existing
`test/05_perf/scv/compile_source_inventory_resource_profile_spec.spl` provides
the admitted N/2N measurement path once a qualified runtime is available.
No exhausted diagnostic build was repeated. Regenerate this manual and retain
actual execution evidence before claiming verification or release admission.
