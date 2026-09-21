# Planner admission portable hashing regression

Scope: production shell hash helpers, invoked from executable SSpec through
`app.io.mod.process_run_timeout`. No compiler bootstrap is performed.

Requirement REQ-PLANNER-PORTABLE-HASH-001: admission hashing must use macOS
`shasum` when GNU `sha256sum` is absent, preserve standard digests and snapshot
records, and refuse failed providers without emitting successful evidence.

| Scenario | Oracle |
| --- | --- |
| Isolated shasum-only PATH | Exit 0, empty stderr, completed fixture verdict; fixture compares known file/text/stream hashes and exact snapshot records |
| Provider emits a digest then fails | Exit 1, empty stdout and stderr |
| Empty input | Exit 0 and exact standard empty SHA-256 digest |

Executable: `test/02_integration/compiler/bootstrap_planner_portable_hash_spec.spl`.
Manual: `doc/06_spec/02_integration/compiler/bootstrap_planner_portable_hash_spec.md`.
The existing shell fixture remains independently runnable. All scenarios are
visible in the manual; no GUI captures apply.

Run the SSpec with a qualified full CLI in native mode. Reject load-only or
empty-success results. Runtime execution and SPipe docgen remain pending;
the known Rust seed must not satisfy these gates.
