# Shared build/test execution scheduling

Status: researched; implementation and executable verification pending.

User explicitly requests shared async/running scheduling, with no lockless map
when unnecessary. This supplements the existing phase2 runner repair goal.

## Retained knowledge

Parent consumed feature_expert/supervised_build/skill.md and layer_expert/
test_runner/skill.md and async_runtime/skill.md under doc/00_llm_process.
A small-model worker independently inspected the test-side execution path;
parent reviewed source and corrected its overly broad JSON-validator claim.

## Evidence

- app.buildrunner.runner reexports common.task_runner.scheduler.
- common.task_runner.scheduler keeps statuses/host reservations under one
  parent; BuildRun/BuildTask provenance is a domain admission contract.
- nogc_sync_mut.test_runner.test_runner_async maintains a separate next-file,
  active-process and admission loop in run_tests_parallel_with_monitoring.
- app.io.process_ops reexports nogc_sync_mut.io.process_ops; build process
  ports and test runner_lifecycle already reach this shared async backend.
- common.task_runner.fiber_scheduler is generic CPU/memory scheduling, but
  its progress-rule over-admission is not an external-process hard-cap policy.
- test_runner.task_runner_adapter classifies aggregate evidence; it does not
  currently replace ordinary per-file scheduling.

No concurrent map writers exist in these scheduling owners. Retain ordinary
parent-owned state. Do not invent BuildTask provenance for ordinary tests,
replace test capture with a blocking build wait, or confuse aggregate-case
integration candidates with the ordinary test runner.
