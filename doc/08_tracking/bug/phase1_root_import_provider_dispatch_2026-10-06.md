# Phase1 root import provider dispatch

The seed formatter spec reported five wrong results: an explicit import of app.devhub.output.format_size called lib.common.format_utils.format_size instead. Application output uses binary units and preserves negative values; the accidentally selected provider uses different formatting.

The flattened loader records root import bindings under `<entry>`, but interpreter overload dispatch ignored those bindings when top-level execution had no active function owner. Use the existing root owner sentinel to resolve explicit imports before historical overload selection. Named function execution continues to use its actual owner.

Two interpreter regressions exercise the flattened loader wire contract with competing providers, including a re-export facade. Both failed before the fix (22 instead of 11) and passed after it. The enforcing 5859375 KiB watchdog recorded peak RSS 4747200 KiB, exit 0, quiescent 1, and maximum sample gap 3036 ms. Evidence is retained under /tmp/simple-import-dispatch-repair.

This is a bootstrap interpreter repair. Verification of the original formatter spec on a rebuilt seed and whole-suite qualification remain pending. No Phase2 admission or release qualification follows from these two tests.
