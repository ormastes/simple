# Concurrency API Misuse System Contract

> This system spec proves the public concurrency API surfaces fail closed at compile time while the approved meaningful API names remain usable. The OS-thread `thread_spawn`, cooperative green queue APIs, low-level green thread APIs, `multicore_green_spawn`, `multicore_green_spawn_sliced`, and pool-backed `task_spawn` facades must reject wrong imports, wrong arity, bad argument types, and direct runtime aliases. The Pure Simple lint at `src/compiler/35.semantics/lint/concurrency_api_misuse.spl` is the authoritative rule map; Rust driver checks are seed compatibility and bootstrap enforcement, not a separate user-facing API source.

<!-- sdn-diagram:id=concurrency_api_misuse_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=concurrency_api_misuse_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

concurrency_api_misuse_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=concurrency_api_misuse_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrency API Misuse System Contract

This system spec proves the public concurrency API surfaces fail closed at compile time while the approved meaningful API names remain usable. The OS-thread `thread_spawn`, cooperative green queue APIs, low-level green thread APIs, `multicore_green_spawn`, `multicore_green_spawn_sliced`, and pool-backed `task_spawn` facades must reject wrong imports, wrong arity, bad argument types, and direct runtime aliases. The Pure Simple lint at `src/compiler/35.semantics/lint/concurrency_api_misuse.spl` is the authoritative rule map; Rust driver checks are seed compatibility and bootstrap enforcement, not a separate user-facing API source.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-concurrency-api-misuse |
| Category | Language / Concurrency |
| Status | Active |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/feature/usage/concurrency_api_misuse_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec proves the public concurrency API surfaces fail
closed at compile time while the approved meaningful API names remain usable.
The OS-thread `thread_spawn`, cooperative green queue APIs, low-level green
thread APIs, `multicore_green_spawn`, `multicore_green_spawn_sliced`, and
pool-backed `task_spawn` facades must reject wrong imports, wrong arity, bad
argument types, and direct runtime aliases.
The Pure Simple lint at `src/compiler/35.semantics/lint/concurrency_api_misuse.spl`
is the authoritative rule map; Rust driver checks are seed compatibility and
bootstrap enforcement, not a separate user-facing API source.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/01_research/local/multicore_green.md

## Syntax

Run the misuse gate:

```sh
SIMPLE_BIN=bin/simple bin/simple test test/03_system/feature/usage/concurrency_api_misuse_spec.spl --mode=interpreter --clean
```

## Examples

- `thread_spawn` must be imported from `std.concurrent.thread`.
- Numbered aliases must remain rejected; use meaningful names such as
  `thread_spawn_with_args`, `spawn_isolated_with_args`, or
  `spawn_limited_with_args` for explicit-argument spawning.
- `thread_spawn_with_args` must stay available as the explicit-argument
  OS-thread API.
- `cooperative_green_spawn` must stay on the cooperative-green surface.
- `multicore_green_spawn` must stay on the multicore-green surface.
- `multicore_green_spawn_sliced` must stay on the multicore-green surface.
- `multicore_green_spawn_sliced` must run and join to a concrete result in
  the public API contract.
- `multicore_green_spawn_sliced` must reject wrong surface imports, wrong
  arity, non-integer initial state, non-function step arguments, and shared
  mutable captures in inline step lambdas.
- `multicore_green_spawn` must accept a single zero-argument closure.
- `multicore_green_set_parallelism` must accept an integer worker count.
- `task_spawn` must stay available as the pool-backed native task API.
- `thread_spawn_with_args` must stay on the OS-thread surface.
- The profile-script API contract checks approved public names before checking
  generated misuse fixtures and the checked-in misuse fixture inventory.
- The Pure Simple lint source keeps E-PAR-001 through E-PAR-006 documented in
  one place and names the Rust checks as seed compatibility only.

## TUI Capture

```text
Simple Test Runner v1.0.0-beta
Running: test/03_system/feature/usage/concurrency_api_misuse_spec.spl
Concurrency API misuse compile errors PASSED
Files: 1
Passed: 7
Failed: 0
```

## Traceability Expectations

- The misuse spec must run each checked-in fixture through `simple check`.
- The checked-in fixture inventory must stay explicit so new misuse fixtures
  cannot appear without updating the public contract count.
- The numbered-alias fixture proves `E-PAR-002` remains a compile-time error,
  while active source/profile scans keep numbered API names out of public
  implementation surfaces.
- Wrong-surface fixtures prove OS-thread, cooperative-green, low-level green,
  multicore-green, and task-pool APIs stay separated.
- Bad-arity and bad-argument fixtures prove spawn APIs fail closed when callers
  do not pass the required closure, state, step function, or worker count.
- Shared-mutable-state fixtures prove green-process closures remain
  share-nothing unless an API explicitly documents a synchronization path.
- The shell profile contract must pass approved public fixtures before running
  misuse fixtures so a broken API cannot be hidden by negative-only coverage.
- The Pure Simple lint source must remain the canonical public concurrency
  misuse rule map; Rust-side checks are seed compatibility and bootstrap
  enforcement.

## Manual Review Notes

- Reviewers should treat numbered aliases only as forbidden input strings; they
  are not API names that application code may import.
- The preferred explicit-argument OS-thread name is `thread_spawn_with_args`.
- Cooperative-green APIs intentionally stay on `std.concurrent.cooperative_green`.
- Low-level green-thread APIs intentionally stay on `std.concurrent.green_thread`.
- Multicore-green APIs intentionally stay on `std.concurrent.multicore_green`.
- `task_spawn` intentionally stays on the lower-level thread-pool surface.
- The generated shell fixtures exercise positive public API names first.
- The checked-in fixtures exercise stable misuse paths that need reviewable
  filenames and generated manual coverage.
- The fixture count is part of the release-visible contract; changing it means
  the tracking row, system plan, and generated manual must change together.
- The default `SIMPLE_BIN` is `bin/simple`; Docker-isolated runs should pass it
  explicitly when the checkout does not contain a local compiler build artifact.
- A stale release wrapper must not be used as proof that a fixture passed or
  failed; the selected compiler must be executable in the test process.
- Compile-error assertions must check both the diagnostic code and the user
  action text so regressions remain understandable.

## Scenarios

### Concurrency API misuse compile errors

#### covers every checked-in misuse fixture

- Count the checked-in concurrency misuse fixtures
   - Expected: fixture_count() equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Count the checked-in concurrency misuse fixtures")
expect(fixture_count()).to_equal(30)
```

</details>

#### keeps Pure Simple lint as the authoritative API misuse rule map

- Open the Pure Simple concurrency API misuse lint
- Verify the lint documents the Rust seed boundary
- Verify the lint owns the public concurrency misuse errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open the Pure Simple concurrency API misuse lint")
val source = read_repo_text("src/compiler/35.semantics/lint/concurrency_api_misuse.spl")
step("Verify the lint documents the Rust seed boundary")
expect(source).to_contain("Rule intents (from Rust seed")
step("Verify the lint owns the public concurrency misuse errors")
expect(source).to_contain("E-PAR-002: numbered-suffix concurrency alias")
expect(source).to_contain("E-PAR-003: concurrency symbol imported from wrong module surface")
expect(source).to_contain("E-PAR-005: direct use of internal rt_pool_* extern symbols outside the facade")
```

</details>

#### keeps approved public API names usable

- Run the profile-script concurrency API contract
   - Expected: code equals `0`
- Verify approved public-name fixtures were checked before misuse fixtures


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the profile-script concurrency API contract")
val (output, code) = run_profile_contract()
expect(code).to_equal(0)
step("Verify approved public-name fixtures were checked before misuse fixtures")
expect(output).to_contain("concurrency_api_contract=true")
expect(output).to_contain("public_multicore_green_sliced_result=19 used_runtime_pool=true")
expect(output).to_contain("positive_fixtures=6")
expect(output).to_contain("fixtures=11")
expect(output).to_contain("misuse_fixtures=11")
expect(output).to_contain("checked_in_misuse_fixtures=30")
expect(output).to_contain("total_misuse_fixtures=41")
```

</details>

#### rejects OS-thread surface misuse

- Reject numbered suffix aliases for OS-thread APIs
- expect compile error
- expect compile error
- expect compile error
- Reject thread_spawn imported from the cooperative-green surface
- expect compile error
- Reject thread_spawn_with_args imported from the cooperative-green surface
- expect compile error
- Reject thread_spawn called with too many arguments
- expect compile error
- Reject thread_spawn called with a non-closure argument
- expect compile error
- Reject task_spawn imported from the OS-thread surface
- expect compile error


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject numbered suffix aliases for OS-thread APIs")
expect_compile_error("thread_spawn_number_suffix_alias.spl", "E-PAR-002", "thread_spawn2 is a numbered name")
expect_compile_error("spawn_isolated_number_suffix_alias.spl", "E-PAR-002", "spawn_isolated2 is a numbered name")
expect_compile_error("spawn_limited_number_suffix_alias.spl", "E-PAR-002", "spawn_limited2 is a numbered name")
step("Reject thread_spawn imported from the cooperative-green surface")
expect_compile_error("thread_spawn_wrong_surface_import.spl", "E-PAR-003", "thread_spawn belongs to std.concurrent.thread")
step("Reject thread_spawn_with_args imported from the cooperative-green surface")
expect_compile_error("thread_spawn_with_args_wrong_surface_import.spl", "E-PAR-003", "thread_spawn_with_args belongs to std.concurrent.thread")
step("Reject thread_spawn called with too many arguments")
expect_compile_error("thread_spawn_wrong_arity.spl", "E-PAR-004", "thread_spawn expects one zero-argument closure")
step("Reject thread_spawn called with a non-closure argument")
expect_compile_error("thread_spawn_bad_arg.spl", "E-PAR-004", "thread_spawn expects one zero-argument closure")
step("Reject task_spawn imported from the OS-thread surface")
expect_compile_error("task_spawn_wrong_surface_import.spl", "E-PAR-001", "task_spawn is not part of the OS-thread facade")
```

</details>

#### rejects cooperative and low-level green-thread surface misuse

- Reject cooperative_green_spawn imported from the OS-thread surface
- expect compile error
- Reject cooperative_green_spawn called with too many arguments
- expect compile error
- Reject cooperative_green_spawn called with a non-closure argument
- expect compile error
- Reject green_spawn imported from the OS-thread surface
- expect compile error
- Reject green_spawn called with too many arguments
- expect compile error
- Reject green_spawn called with a non-closure argument
- expect compile error


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject cooperative_green_spawn imported from the OS-thread surface")
expect_compile_error("cooperative_green_wrong_surface_import.spl", "E-PAR-003", "cooperative_green_spawn belongs to std.concurrent.cooperative_green")
step("Reject cooperative_green_spawn called with too many arguments")
expect_compile_error("cooperative_green_wrong_arity.spl", "E-PAR-004", "cooperative_green_spawn expects one share-nothing zero-argument closure")
step("Reject cooperative_green_spawn called with a non-closure argument")
expect_compile_error("cooperative_green_bad_arg.spl", "E-PAR-004", "cooperative_green_spawn expects one share-nothing zero-argument closure")
step("Reject green_spawn imported from the OS-thread surface")
expect_compile_error("green_spawn_wrong_surface_import.spl", "E-PAR-003", "green_spawn belongs to std.concurrent.green_thread")
step("Reject green_spawn called with too many arguments")
expect_compile_error("green_spawn_wrong_arity.spl", "E-PAR-004", "green_spawn expects one share-nothing zero-argument closure")
step("Reject green_spawn called with a non-closure argument")
expect_compile_error("green_spawn_bad_arg.spl", "E-PAR-004", "green_spawn expects one share-nothing zero-argument closure")
```

</details>

#### rejects multicore-green runtime-pool facade misuse

- Reject multicore_green_spawn imported from the OS-thread surface
- expect compile error
- Reject multicore_green_spawn called with too many arguments
- expect compile error
- Reject multicore_green_spawn called with a non-closure argument
- expect compile error
- Reject multicore_green_set_parallelism called with text
- expect compile error
- Reject direct rt_pool_* access that bypasses the public multicore_green facade
- expect compile error
- Reject direct rt_pool_* counter access that bypasses the public multicore_green facade
- expect compile error
- Reject multicore_green_spawn_sliced imported from the OS-thread surface
- expect compile error
- Reject multicore_green_spawn_sliced called with too few arguments
- expect compile error
- Reject multicore_green_spawn_sliced called with non-integer initial state
- expect compile error
- Reject multicore_green_spawn_sliced called with non-function step argument
- expect compile error


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject multicore_green_spawn imported from the OS-thread surface")
expect_compile_error("multicore_green_wrong_surface_import.spl", "E-PAR-003", "multicore_green_spawn belongs to std.concurrent.multicore_green")
step("Reject multicore_green_spawn called with too many arguments")
expect_compile_error("multicore_green_wrong_arity.spl", "E-PAR-004", "multicore_green_spawn expects one share-nothing zero-argument closure")
step("Reject multicore_green_spawn called with a non-closure argument")
expect_compile_error("multicore_green_bad_arg.spl", "E-PAR-004", "multicore_green_spawn expects one share-nothing zero-argument closure")
step("Reject multicore_green_set_parallelism called with text")
expect_compile_error("multicore_green_parallelism_bad_arg.spl", "E-PAR-004", "integer worker count")
step("Reject direct rt_pool_* access that bypasses the public multicore_green facade")
expect_compile_error("multicore_green_direct_rt_pool_access.spl", "E-PAR-005", "direct rt_pool_* access bypasses the public multicore_green facade")
step("Reject direct rt_pool_* counter access that bypasses the public multicore_green facade")
expect_compile_error("multicore_green_direct_rt_pool_counter_access.spl", "E-PAR-005", "direct rt_pool_* access bypasses the public multicore_green facade")
step("Reject multicore_green_spawn_sliced imported from the OS-thread surface")
expect_compile_error("multicore_green_sliced_wrong_surface_import.spl", "E-PAR-003", "multicore_green_spawn_sliced belongs to std.concurrent.multicore_green")
step("Reject multicore_green_spawn_sliced called with too few arguments")
expect_compile_error("multicore_green_sliced_wrong_arity.spl", "E-PAR-004", "multicore_green_spawn_sliced expects integer state and step function")
step("Reject multicore_green_spawn_sliced called with non-integer initial state")
expect_compile_error("multicore_green_sliced_bad_state_arg.spl", "E-PAR-004", "multicore_green_spawn_sliced expects integer state and step function")
step("Reject multicore_green_spawn_sliced called with non-function step argument")
expect_compile_error("multicore_green_sliced_bad_step_arg.spl", "E-PAR-004", "multicore_green_spawn_sliced expects a step function as the second argument")
```

</details>

#### rejects shared mutable state in green-process closures

- Reject green_spawn closures that read module-level mutable variables
- expect compile error
- Reject cooperative_green_spawn closures that mutate captured variables
- expect compile error
- Reject multicore_green_spawn closures that read module-level mutable variables
- expect compile error
- Reject multicore_green_spawn_sliced inline step lambdas that mutate shared variables
- expect compile error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject green_spawn closures that read module-level mutable variables")
expect_compile_error("green_spawn_shared_var_capture.spl", "E-PAR-006", "green_spawn closure must not capture shared mutable state")
step("Reject cooperative_green_spawn closures that mutate captured variables")
expect_compile_error("cooperative_green_shared_var_capture.spl", "E-PAR-006", "cooperative_green_spawn closure must not capture shared mutable state")
step("Reject multicore_green_spawn closures that read module-level mutable variables")
expect_compile_error("multicore_green_shared_var_capture.spl", "E-PAR-006", "multicore_green_spawn closure must not capture shared mutable state")
step("Reject multicore_green_spawn_sliced inline step lambdas that mutate shared variables")
expect_compile_error("multicore_green_sliced_shared_var_capture.spl", "E-PAR-006", "multicore_green_spawn_sliced closure must not capture shared mutable state")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
