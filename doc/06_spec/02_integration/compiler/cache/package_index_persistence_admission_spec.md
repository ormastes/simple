# Persisted package index admission

Source: `test/02_integration/compiler/cache/package_index_persistence_admission_spec.spl`.
Requirement: `PSI-REQ-004`. Status: UNEXECUTED.
This hand-maintained manual awaits admitted SSpec execution and docgen.

Each scenario publishes through `package_module_index_publish_if_current_v1`,
mutates actual fixture storage, and reads through the production admission
owner. Setup/teardown isolate and remove the fixture root.

| Scenario | Mutation and required rejection | Recovery assertion |
|---|---|---|
| Payload tamper | Append bytes to the selected generation; expect `generation-digest-mismatch`, no decoded value, unchanged pointer and preserved corrupt bytes | Restore exact original bytes; expect original admitted digest |
| Invalid pointer | Replace CURRENT with a non-digest; expect `missing-or-invalid-generation`, no decoded value, prior generation bytes preserved | Restore pointer; CAS publication and admission must work, proving no stranded lock |
| Empty pointer | Truncate CURRENT; expect `missing-or-invalid-generation` and no implicit rewrite/deletion | Restore pointer; CAS publication and admission must work |
| Absent generation | Point CURRENT at a valid digest with no matching payload; expect `generation-unavailable` and prior generation bytes preserved | Restore original pointer; expect original admitted digest |

These storage tests do not prove whole-compiler no-scan behavior, end-to-end
cache reuse or crash recovery. The broad acceptance harness still needs real
production instrumentation. No runtime PASS or RED/GREEN evidence is claimed.
