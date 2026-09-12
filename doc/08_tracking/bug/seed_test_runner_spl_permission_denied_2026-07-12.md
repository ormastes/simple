# Seed Test Runner Executes Simple Source as a Host Program
**Status:** OPEN (2026-09-12, re-verified: bin/simple test test/03_system/os/simpleos_memory_leveling_gpu_nic_dma_spec.spl -> 7 passed, 1 failed, still reproduces)

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

## Triage 2026-09-12
Rule B: ran `bin/simple test test/03_system/os/simpleos_memory_leveling_gpu_nic_dma_spec.spl` on the deployed seed; 1 of 8 checks still fail, so this record still reproduces. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
