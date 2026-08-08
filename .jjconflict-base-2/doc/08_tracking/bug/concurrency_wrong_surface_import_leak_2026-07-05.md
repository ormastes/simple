# Concurrency Wrong-Surface Import Leak

Status: Closed

## Summary

`simple check` previously accepted at least one concurrency API from the wrong
public surface:

```simple
use std.concurrent.cooperative_green.{thread_spawn_with_args}
```

`thread_spawn_with_args` belongs to `std.concurrent.thread`, not
`std.concurrent.cooperative_green`. The checked-in misuse fixture
`test/fixtures/concurrency_api_misuse/thread_spawn_with_args_wrong_surface_import.spl`
now fails through the active lightweight check worker and the Rust fallback
check helper.

## Evidence

Command:

```sh
src/compiler_rust/target/debug/simple check test/fixtures/concurrency_api_misuse/thread_spawn_with_args_wrong_surface_import.spl
```

Former observed failure:

```text
All checks passed (1 file(s))
```

Closing evidence:

```sh
SIMPLE_BIN=src/compiler_rust/target/debug/simple sh test/05_perf/profile_scripts/concurrency_api_contract_test.shs
```

Observed:

```text
concurrency_api_contract=true
fixtures=11
misuse_fixtures=11
checked_in_misuse_fixtures=30
total_misuse_fixtures=41
positive_fixtures=6
```

## Impact

Concurrency surface-boundary evidence is restored for the checked public
OS-thread, cooperative-green, multicore-green, and task-pool API fixtures.

## Fix

The active Pure Simple check worker now rejects wrong-surface public
concurrency imports, numbered aliases, direct `rt_pool_*` externs, and the
documented call-shape/share-nothing misuse fixtures. The Rust fallback check
helper also recognizes `thread_spawn_with_args` as an OS-thread-only API.
