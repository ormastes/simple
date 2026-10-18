# Windows smux bypasses the requested SOSIX host boundary

Status: source repair authored; admitted native execution pending.

At `58c2a34b106af1ab0abbf5e2c353845805f9e951`, smux's legacy stdin loop
declared/called `rt_read_stdin_line` in the application. Process/time/sleep and
PTY/console used ordinary facades directly. The user requires SOSIX routing.

Both independent Windows product fixtures imported `app.io.mod.thread_sleep_ms`.
That resolves to `nogc_sync_mut.io.thread.thread_sleep_ms`, which runs
`/bin/sh -c sleep ...` and formats 10ms as `0.10` seconds. A native Windows
fixture therefore depends on an external POSIX shell and has incorrect delay
semantics. This is an observed source defect, not an executed timing result.

Repair: exact synchronous SOSIX aliases above existing canonical owners.
Fixture sleep now uses `concurrent.thread.thread_sleep`, whose native ABI is
`rt_thread_sleep(millis)`. Product partial-transfer, sentinel, deadline, provider
availability and ownership behavior is unchanged. Tagged text stdin is routed
through `sffi.host.read_stdin_line`; optional-pointer stdin must not replace it.

Controls: `test/03_system/tools/smux_sosix_boundary_spec.spl` (source architecture
and negative controls) and `test/fixtures/compiler_entrypoint/smux_sosix_host`
(real argv/file/PID/time/sleep/Unicode stdin/EOF). Both independent Windows smux
fixtures retain their real I/O, resize and cleanup assertions. No native
compiler was invoked for this source-only lane. Root must bind execution to an
admitted producer and source identity before marking the bug verified.
