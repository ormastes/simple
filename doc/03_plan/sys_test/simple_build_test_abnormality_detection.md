# System Test Plan: Simple Build/Test Abnormality Detection

## Scenario flow

1. `Create a bounded execution resource scope`
2. `Run a child tree and collect resource evidence`
3. `Classify termination from affirmative evidence`
4. `Record spans and work counters`
5. `Compare against an approved cohort baseline`
6. `Explain the budget and anomaly decisions`

## Requirement matrix

| Case | Requirements | Evidence |
|---|---|---|
| Direct child + grandchild allocation | REQ-002, REQ-004 | nonzero direct evidence; exact/sampled tree includes descendant |
| SIGSEGV and external SIGTERM | REQ-003 | crash vs unverified external classification |
| memory/PID/watchdog event | REQ-003, REQ-011 | proven independent budget cause |
| interpreter/native and aspect identities | REQ-007 | distinct canonical cohorts |
| candidate +25% | REQ-008, REQ-009 | anomaly detected; approved baseline unchanged |
| missing required phase | REQ-010 | incomplete/suspicious evidence, never speedup PASS |
| rare memory spike | REQ-009 | sample retained and tail status exposed |
| incremental edit | REQ-010 | cache hit/miss and invalidation reason recorded |
| N/2N/4N/8N quadratic fixture | REQ-012 | exponent crosses configured threshold |

## Platform rows

- Linux current host: exact cgroup v2 when delegated/available; otherwise fallback quality and current-host provider contract tests.
- Windows: legacy execution remains functional with unavailable evidence; observed Job accounting/enforcement acceptance is blocked with owner, implementation steps, and resume command in `doc/08_tracking/todo/simple_build_test_abnormality_windows_job_receipt_2026-08-24.md`.
- macOS: process-group/RLIMIT execution remains functional with unavailable evidence; observed direct-child/sampled-tree acceptance is blocked with owner, implementation steps, and resume command in `doc/08_tracking/todo/simple_build_test_abnormality_macos_receipt_2026-08-24.md`.

## Open acceptance debt

The executable spec does not yet cover every selected requirement through a
production path. The authoritative completion checklist is
`doc/08_tracking/todo/simple_build_test_abnormality_acceptance_completion_2026-08-25.md`.

The executable scenario lives under `test/03_system/app/perf/feature/`; its mirrored manual is Markdown only under `doc/06_spec/03_system/app/perf/feature/`.
