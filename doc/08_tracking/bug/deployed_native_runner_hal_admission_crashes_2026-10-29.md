# Deployed native runner crashes before HAL examples

Status: OPEN — reproduced with LLDB; deployed executable is not qualified for
HAL evidence. No Phase 2 rebuild was performed.

## Artifact and reproduction

- Source inspection: commit `2618f6fda7f`.
- Executable: `/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple`.
- SHA-256: `2a59a9cbc17e7e078b2b4dbb44bad7f865a0aa201cbd21405059b412c6c033ba`.
- Existing input: `/tmp/sosix-hal-latest-20261029/test/03_system/runtime/sosix_host_runtime_access_spec.spl`.
- Working directory: isolated checkout `/tmp/astra-hal-native-crash-20261029`.

Run with `SIMPLE_LIB=src`, arguments `test <input> --mode=native
--no-cover-check`. LLDB's `--batch -o run -k 'bt 30'` captures the crash
backtrace (use `-k` for commands on abnormal stop).

The default session route discovers one file, then calls a null function pointer:

```text
EXC_BAD_ACCESS address=0x0
0  0x0
1  daemon_sdk.client.daemon_ensure_running +196
2  daemon_sdk.client.daemon_ensure_responsive +152
3  test_daemon.client.test_daemon_ensure_responsive +520
4  test_runner_main.run_tests +5040
```

Disassembly at the caller is `ldr x8, [x20]; mov x0, x20; blr x8`.
Current `src/app/test_daemon/client.spl` no longer calls the generic SDK's
start callback: it checks an existing daemon lock and pings that daemon.
This proves the deployed executable does not implement that current source
path. Re-editing the already corrected client cannot repair this executable.

## Direct-route regression

Adding `--no-session-daemon` bypasses the first crash but still exits 139.
It prints `[route] mode=native`, then an invalid-array-handle diagnostic
(`probable compiler/FFI ABI mismatch`) and crashes before reporting examples:

```text
EXC_BAD_ACCESS address=0x8
0  perf.execution_metrics.evaluate_resource_budget +372
1  io.resource_scope.run_in_execution_resource_scope +468
2  test_runner_execute._run_scoped_child +528
3  test_runner_execute.run_test_file_native +2444
4  test_runner_main.run_single_test +3888
```

The faulting instruction is `ldp x10, x11, [x8, #0x8]` with a null base.
The invalid handle varies with ASLR. This localizes the second failure to
runner resource-result/budget handling; it does not establish which producer
or ABI conversion corrupted the value. Do not claim a HAL implementation
failure from these traces or disable resource limits to make tests appear green.

## Evidence and completion criteria

Local evidence: `/tmp/astra-hal-native-lldb-stack.log`,
`/tmp/astra-hal-native-direct.log`, and
`/tmp/astra-hal-native-direct-lldb.log`. Both routes were tested once per
distinct diagnostic change. No generated HAL test result passed.

Completion requires an already available source-matched runner, or an explicitly
authorized non-Phase-2 runner artifact build, followed by both default-session
and `--no-session-daemon` executions. Require nonzero executed examples and
real assertion results, no signal exit, and retained resource enforcement.
The currently permitted existing artifact fails this gate; Phase 2 rebuilds
remain prohibited. Source-level tests of current daemon readiness cannot
substitute for deployed executable qualification.
