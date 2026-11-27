# Resident thread-context object policy

Source: `test/01_unit/compiler/backend/runtime_xray_context_policy_v1_spec.spl`.
Requirements: B02 (off-path isolation), T01 (real thread owner), C01 (object identity).

The full SSpec runner has not executed this file. Its production helpers are included in the retained native 57-assertion projection.

| Scenario | Action | Required result |
|---|---|---|
| Tracing off | Query an unresolved or unsupported target with hooks disabled. | No new flags, cache suffix or target rejection. |
| Supported source runtime | Request hooks for exact Linux GNU x86-64 or AArch64 with core-C source ownership. | Select the optional object variant. This alone does not admit tracing. |
| Unsupported ownership | Request host aliases, another platform, Rust owners or Stage4/archive composition. | Refuse before runtime object compilation. |
| Cache separation | Compare enabled and disabled policies. | Only enabled identity gains the thread-context token. |
| Actual source flags | Resolve macros for runtime_thread, runtime_pool and unrelated source names. | Only an actually selected thread/pool source receives the macro. The current core-C list contains runtime_thread; this test does not claim runtime_pool is linked. |

Real runtime entry, pre-existing worker attachment and stop/drain integration require their separate native fixtures.
