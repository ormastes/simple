# Green Thread Spec Runner Mismatch

Date: 2026-06-11
Status: closed
Owner: multicore-green lane

## Summary

The earlier interpreter-mode runner mismatch for minimal green-thread and
cooperative-green queue assertions is closed.

- `simple run` on a tiny `green_spawn_value(23)` probe passes.
- `simple test` on the equivalent one-`it` spec now also passes.

This is distinct from the earlier SMF/native cooperative runtime blockers,
which were already closed. The runner-side mismatch itself is now fixed as
well.

## Repro

Passing direct run shape:

```sh
./src/compiler_rust/target/debug/simple run build/test/cooperative_green_spec_runner_mismatch/green_probe_run.spl
```

Passing test-runner shape:

```sh
./src/compiler_rust/target/debug/simple test build/test/cooperative_green_spec_runner_mismatch/green_probe_spec.spl --mode=interpreter --clean
```

Pinned executable regression coverage:

- `test/03_system/feature/usage/cooperative_green_spec_runner_mismatch_spec.spl`

## Current Impact

- `test/01_unit/lib/nogc_async_mut/green_thread_spec.spl` passes.
- `test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl` passes.
- `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl` passes.
- `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl` passes.

## Resolution

The root issue was in the interpreter-mode `simple test` state-reset path. The
runner preserved selective stdlib/module cache state across tests in a way that
the plain `simple run` path did not, which let hosted green/concurrency specs
observe stale behavior. Switching interpreter-mode test execution to a full
module-cache clear restored alignment with the direct interpreter path.

## Exit Evidence

- minimal `green_spawn_value(23)` one-`it` SSpec passes under
  `simple test --mode=interpreter`
- `green_thread_spec.spl` and `cooperative_green_spec.spl` pass
- hosted SimpleOS cooperative/multicore specs pass without downgrading
  their green-thread assertions
