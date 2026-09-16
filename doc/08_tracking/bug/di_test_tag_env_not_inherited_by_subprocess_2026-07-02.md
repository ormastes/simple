---
id: di_test_tag_env_not_inherited_by_subprocess_2026-07-02
status: OPEN
severity: medium
discovered: 2026-07-02
discovered_by: test/03_system/feature/features/di_extensions_system_spec.spl (5/10 failures while restoring DiContainer.has())
related: src/app/test_runner_new/test_runner_main.spl
related: src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl
related: src/compiler/00.common/di.spl
---

# `# @di_test` tag does not bypass the DI system-test lock in spawned test subprocess

## Summary

`run_single_test` (src/app/test_runner_new/test_runner_main.spl:614-623) sets
`SIMPLE_SYSTEM_TEST` / `SIMPLE_DI_TEST` via `env_set()` in the **parent**
runner process before dispatching to `run_test_file_interpreter` /
`run_test_file_smf` (src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl),
which run the spec's `it` blocks in a **spawned child process**
(`process_run_timeout` / `find_simple_binary()` + `build_child_args`).

`DiContainer.di_is_system_test_locked()` (src/compiler/00.common/di.spl) reads
`SIMPLE_SYSTEM_TEST` / `SIMPLE_DI_TEST` via `rt_env_get` inside that child
process. Empirically, the child never observes `SIMPLE_DI_TEST=1` even though:

- `file_has_di_test_tag(file_path)` correctly returns `true` for a file
  containing `# @di_test` (verified directly).
- Forcing `SIMPLE_SYSTEM_TEST=1 SIMPLE_DI_TEST=1` in the *shell* that invokes
  `bin/simple test ...` makes no difference (parent runner still overwrites
  with its own env_set calls based on its own is_system/tag detection, and the
  child still sees the container as locked).

Net effect: any spec tagged `# @di_test` under a `test/*/system/` or
`test/*/feature/` path that calls DI mutation methods (`bind`, `bind_instance`,
`bind_for_profile`, `bind_tagged`) during setup is silently blocked by the
lock, producing cascading assertion failures unrelated to the feature under
test.

## Reproduction

```
bin/simple test test/03_system/feature/features/di_extensions_system_spec.spl --no-cache
```

5/10 examples fail. Isolated via bisection: an `it` block that only calls
`extensions.has_binding(...)` / `.has(...)` on a container that never had
`bind*` called on it passes; any `it` block that calls `bind_instance()`
before `.lock()` (expecting it to succeed because of `# @di_test`) fails with
"DI bind_instance(...) rejected: container locked in system test mode" —
confirming the tag isn't reaching the child process's env.

The identical failure reproduces on the pre-restructure duplicate
`test/system/features/di_extensions_system_spec.spl`, confirming this is a
systemic runner/subprocess-env issue, not specific to one file.

## Suspected root cause

`SIMPLE_DI_TEST` / `SIMPLE_SYSTEM_TEST` are set via `env_set()` (-> `rt_env_set`)
in the parent runner process only. Whatever `rt_process_run*` uses to spawn
the child (interpreter subprocess) either snapshots the environment before
the runner's `env_set` calls apply, or does not propagate process-level env
mutations performed via `rt_env_set` to spawned children. Passing the lock
state explicitly as a CLI flag/arg to the child (already threaded through
`build_child_args`) rather than relying on env inheritance would sidestep the
issue.

## Scope note

Not part of the 2026-07-02 "5 lost fixes" restoration pass. `DiContainer.has()`
(the actual lost fix for this file) is implemented and verified correct in
isolation — this failure is a pre-existing, unrelated subprocess/env-propagation
bug in the test runner infrastructure.
