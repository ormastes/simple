# Concurrency API Misuse System Contract

> This system spec proves the public pherallel/concurrency API surfaces fail closed at compile time while the approved meaningful API names remain usable. The OS-thread `thread_spawn`, cooperative green queue APIs, low-level green thread APIs, and `multicore_green_spawn` runtime-pool facade must reject wrong imports, wrong arity, bad argument types, and numbered alias names.

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
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrency API Misuse System Contract

This system spec proves the public pherallel/concurrency API surfaces fail closed at compile time while the approved meaningful API names remain usable. The OS-thread `thread_spawn`, cooperative green queue APIs, low-level green thread APIs, and `multicore_green_spawn` runtime-pool facade must reject wrong imports, wrong arity, bad argument types, and numbered alias names.

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

This system spec proves the public pherallel/concurrency API surfaces fail
closed at compile time while the approved meaningful API names remain usable.
The OS-thread `thread_spawn`, cooperative green queue APIs, low-level green
thread APIs, and `multicore_green_spawn` runtime-pool facade must reject wrong
imports, wrong arity, bad argument types, and numbered alias names.

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
./src/compiler_rust/target/debug/simple test test/03_system/feature/usage/concurrency_api_misuse_spec.spl --mode=interpreter --clean
```

## Examples

- `thread_spawn` must be imported from `std.concurrent.thread`.
- `cooperative_green_spawn` must stay on the cooperative-green surface.
- `multicore_green_spawn` must accept a single zero-argument closure.
- `multicore_green_set_parallelism` must accept an integer worker count.
- Numbered aliases such as `thread_spawn2` must be rejected.
- The profile-script API contract checks approved public names before checking
  misuse fixtures.

## Scenarios

### Concurrency API misuse compile errors

#### covers every checked-in misuse fixture

- Count the checked-in concurrency misuse fixtures
   - Expected: fixture_count() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Count the checked-in concurrency misuse fixtures")
expect(fixture_count()).to_equal(13)
```

</details>

#### keeps approved public API names usable

- Run the profile-script concurrency API contract
   - Expected: code equals `0`
- Verify approved public-name fixtures were checked before misuse fixtures


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the profile-script concurrency API contract")
val (output, code) = run_profile_contract()
expect(code).to_equal(0)
step("Verify approved public-name fixtures were checked before misuse fixtures")
expect(output).to_contain("concurrency_api_contract=true")
expect(output).to_contain("positive_fixtures=3")
expect(output).to_contain("fixtures=4")
```

</details>

#### rejects OS-thread surface misuse and numbered aliases

- Reject thread_spawn imported from the cooperative-green surface
- expect compile error
- Reject thread_spawn called with too many arguments
- expect compile error
- Reject thread_spawn called with a non-closure argument
- expect compile error
- Reject numbered thread_spawn aliases
- expect compile error


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject thread_spawn imported from the cooperative-green surface")
expect_compile_error("thread_spawn_wrong_surface_import.spl", "E-PAR-003", "thread_spawn belongs to std.concurrent.thread")
step("Reject thread_spawn called with too many arguments")
expect_compile_error("thread_spawn_wrong_arity.spl", "E-PAR-004", "single zero-argument value closure")
step("Reject thread_spawn called with a non-closure argument")
expect_compile_error("thread_spawn_bad_arg.spl", "E-PAR-004", "pass a closure")
step("Reject numbered thread_spawn aliases")
expect_compile_error("numbered_thread_spawn_alias_import.spl", "E-PAR-002", "numbered name and is not a public API")
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
expect_compile_error("cooperative_green_wrong_arity.spl", "E-PAR-004", "single zero-argument value closure")
step("Reject cooperative_green_spawn called with a non-closure argument")
expect_compile_error("cooperative_green_bad_arg.spl", "E-PAR-004", "pass a closure")
step("Reject green_spawn imported from the OS-thread surface")
expect_compile_error("green_spawn_wrong_surface_import.spl", "E-PAR-003", "green_spawn belongs to std.concurrent.green_thread")
step("Reject green_spawn called with too many arguments")
expect_compile_error("green_spawn_wrong_arity.spl", "E-PAR-004", "single zero-argument value closure")
step("Reject green_spawn called with a non-closure argument")
expect_compile_error("green_spawn_bad_arg.spl", "E-PAR-004", "pass a closure")
```

</details>

#### rejects multicore-green runtime-pool facade misuse

- Reject multicore_green_spawn called with too many arguments
- expect compile error
- Reject multicore_green_spawn called with a non-closure argument
- expect compile error
- Reject multicore_green_set_parallelism called with text
- expect compile error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject multicore_green_spawn called with too many arguments")
expect_compile_error("multicore_green_wrong_arity.spl", "E-PAR-004", "single zero-argument value closure")
step("Reject multicore_green_spawn called with a non-closure argument")
expect_compile_error("multicore_green_bad_arg.spl", "E-PAR-004", "pass a closure")
step("Reject multicore_green_set_parallelism called with text")
expect_compile_error("multicore_green_parallelism_bad_arg.spl", "E-PAR-004", "single integer worker count")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
