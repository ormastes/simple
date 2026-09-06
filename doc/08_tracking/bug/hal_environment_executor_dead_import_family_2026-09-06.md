# Six HAL environment-executor specs import test modules that exist nowhere — they can never execute

**Date:** 2026-09-06
**Found by:** sspec score-80 wave 12G (modernizing the `hal_environment_*` executor specs)

## Symptom

Every spec in this family fails JIT-strict load with E1034
`cannot resolve import app.test.hal_environment_executor` (and the
per-executor variants). `executed=0` in every verdict — the scenarios
have never run on this lane.

## The dead imports

| Spec | Dead import |
|---|---|
| `test/02_integration/app/hal_environment_physical_executor_spec.spl:33` | `app.test.hal_environment_executor.{...}` |
| `test/02_integration/app/hal_environment_entropy_executor_spec.spl:32` | `app.test.hal_environment_entropy_executor.*` |
| `test/02_integration/app/hal_environment_socket_executor_spec.spl:32` | `app.test.hal_environment_socket_executor.*` |
| `test/02_integration/app/hal_environment_file_executor_spec.spl:5` | `app.test.hal_environment_file_executor.*` |
| `test/02_integration/app/hal_environment_process_timeout_spec.spl:5` | `app.test.hal_environment_executor.{...}` |
| `test/02_integration/app/hal_tagged_environment_binding_spec.spl:6` | `app.test.hal_environment_executor.{...}` |

No `app/test/hal_environment*` module exists anywhere under `src/` or
`test/` (`find` over both trees returns nothing), and the symbols the
specs pull through those imports (`HostedProcessPollEnvExecutorV1`,
`EnvExecutorPolicyV1`, `EnvSandboxExecutorV1`, `environment_instruction`
module members) have zero definitions in `src/` — they exist only inside
these spec files.

## Impact

The whole `mcdc_hal_runtime_hardening` environment-executor surface is
either unimplemented or was deleted without updating its spec family.
The specs were modernized to raw=100 on source-contract/structural
assertions in waves 12C–12G, but their runtime scenarios stay
`executed=0` until the executor module exists.

## Unblock condition

Implement (or restore) the `app.test.hal_environment_executor` module
family — or the `src/` product surface it was meant to wrap — so the six
specs' imports resolve and their scenarios execute.
