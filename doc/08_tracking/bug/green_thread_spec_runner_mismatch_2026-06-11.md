# Green Thread Spec Runner Mismatch

Date: 2026-06-11
Status: open
Owner: multicore-green lane

## Summary

Minimal green-thread and cooperative-green queue assertions currently diverge
between `simple run` and `simple test`.

- `simple run` on a tiny `green_spawn_value(23)` probe passes.
- `simple test` on the equivalent one-`it` spec fails.

This is not the same as the earlier SMF/native cooperative runtime blockers.
Those runtime-path issues are now closed for the direct run surfaces. The
remaining open boundary is the SSpec/test-runner path for green/cooperative
queue assertions.

## Repro

Passing direct run shape:

```sh
./src/compiler_rust/target/debug/simple run build/test/cooperative_green_spec_runner_mismatch/green_probe_run.spl
```

Failing test-runner shape:

```sh
./src/compiler_rust/target/debug/simple test build/test/cooperative_green_spec_runner_mismatch/green_probe_spec.spl --mode=interpreter --clean
```

Pinned executable evidence:

- `test/03_system/feature/usage/cooperative_green_spec_runner_mismatch_spec.spl`

## Current Impact

- `test/01_unit/lib/nogc_async_mut/green_thread_spec.spl` fails.
- `test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl` fails.
- `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl` fails.
- `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl` is
  not currently trustworthy as hosted green evidence until the underlying
  runner mismatch is closed.

## Working Theory

The mismatch is in the SSpec/test-runner path, not in the direct queue
semantics. The runner or matcher surface appears to interact badly with
green-thread stateful assertions that pass under direct execution.

## Exit Criteria

- minimal `green_spawn_value(23)` one-`it` SSpec passes under
  `simple test --mode=interpreter`
- `green_thread_spec.spl` and `cooperative_green_spec.spl` pass again
- hosted SimpleOS cooperative/multicore specs pass again without downgrading
  their green-thread assertions
