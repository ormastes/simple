# Seed Test Runner Executes Simple Source as a Host Program

## Status

Fixed on 2026-07-12. All runner/client/daemon binary selectors now reject a
`.spl` `argv[0]` before considering it an executable.

## Reproduction

```sh
src/compiler_rust/target/bootstrap/simple test --no-session-daemon \
  test/03_system/os/simpleos_memory_leveling_gpu_nic_dma_spec.spl \
  --mode=interpreter
```

The rebuilt seed dispatches to `test_runner_single.spl`, then passes that source
path to `timeout` as though it were a host executable:

```text
timeout: failed to run command 'src/app/test_runner_new/test_runner_single.spl': Permission denied
```

The daemon-client path fails identically with `test_runner_client.spl`.

## Fix

`test_runner_client.spl`, `test_runner_single.spl`, `test_daemon/main.spl`, and
`test_daemon/light_daemon.spl` require a non-`.spl` existing `argv[0]` before
using it as the compiler binary. The source-contract regression is
`test/01_unit/app/test_runner_binary_source_guard_spec.spl`.
