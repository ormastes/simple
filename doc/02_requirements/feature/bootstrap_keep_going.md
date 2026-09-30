# Bootstrap collect-all requirements

Selected by the user's explicit request on 2026-09-30: local/bootstrap builds
continue independent module work after failures, retain valid caches, and report
failure after collecting outcomes. CI defaults to fail-fast. Either environment
can explicitly select either policy; the last CLI policy flag wins.

| ID | Acceptance criterion |
|---|---|
| REQ-KG-001 | Host/local/bootstrap compilation defaults to collect-all; CI defaults to fail-fast. Explicit `--keep-going` or `--fail-fast` overrides that default in either environment; ordered CLI flags use the last occurrence. `SIMPLE_COMPILE_FAIL_FAST` remains the canonical environment policy. |
| REQ-KG-002 | A HIR worker crash durably identifies its active module, leaves that module terminal, and permits unfinished independently processable modules to be attempted by a replacement. |
| REQ-KG-003 | Successful existing HIR entries remain reusable only under their existing source, whole-closure surface, compiler identity, mode, and codec validity rules. Failures do not delete the cache. |
| REQ-KG-004 | Any module diagnostic, worker crash, worker launch failure, or blocked prerequisite yields a nonzero aggregate. A failed shard pass never proceeds to the final worker, linking, or candidate admission. |
| REQ-KG-005 | Each crashed module is attempted at most once per invocation. A replacement requires newly attributed module progress; crashes before module claim and unavailable prerequisites do not cause retry loops. |
| REQ-KG-006 | Module outcomes distinguish successful lowering, diagnostics, crash, and blocked work. Poisoned dependency work remains blocked; prerequisites and semantic checks are never bypassed. |

Scope: scheduling, failure policy, durable invocation receipts, cache reuse, and
focused regression evidence. Memory snapshot publication and underlying memory
fault investigation are outside this change.

Validation must distinguish executable behavior from source inspection. Full
bootstrap is not required for this scoped change. An unavailable admitted runtime
is reported as an evidence gap, never as a passing behavioral test.
