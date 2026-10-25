# Bootstrap owner snapshots refuse unavailable native dictionary extent

Status: OPEN; native producer qualification pending. This lane has not reproduced the runtime defect or changed generic Dict semantics.

Astra's provenance-foundation review identified that native `Dict.len()` can return `-1` in this repository. The foundation now maintains a scalar inserted-origin count for its ordinary empty-origin fast path. The new cold snapshot boundary requires an authoritative extent before materializing/sorting key arrays; `bootstrap_fn_registry_snapshot_encode_budgeted_v1` explicitly refuses a negative extent or a mismatch with the actual key inventory. It never guesses an empty map or allocates an unbounded fallback key snapshot.

Trigger: a qualified native producer invokes the twenty-map snapshot exporter and any semantic dictionary reports a negative extent. Expected result is a bounded explicit error with the input owner unchanged. This is a compiler/runtime prerequisite, not a successful snapshot or a reason to switch to the Rust seed. Record the actual admitted producer/source/runtime/cache identity and a focused real-dictionary reproduction before repairing the owning primitive or introducing owner-maintained semantic counters.

Affected source: `src/compiler/50.mir/bootstrap_fn_registry_snapshot_v1.spl`, `_snapshot_count_v1` and the guarded key-snapshot boundary. Native execution and performance acceptance remain UNRUN; no SOURCE or bootstrap worker admission is granted.
