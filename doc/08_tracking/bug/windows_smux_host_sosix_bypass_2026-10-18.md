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

## Source verification, 2026-10-18

Focused controls passed for eleven boundary sources, seven rejecting controls,
two admitting controls, and all thirty-three alias declarations. Normalized
comparison found no unrelated behavior changes in the ten migrated consumers.
All twenty-seven smux product files contain no raw extern declarations or
forbidden async-SOSIX imports. Working/staged environment guards, whitespace,
and executable-spec layout (zero misplaced specs) passed.

The canonical capsule guard remains FAIL only for unchanged R4 line limits:
common contracts vfs_contract_v1.spl has 385 lines and async sosix/fs.spl has
335, versus 300. Their blobs equal baseline HEAD (e420c119a7d7412829a0de435e71fc6880faa28a
and f146445de2532946d2fe08fa669d1d4023eb9984). Selftest and R1/R2/R3 passed;
R5 reports 5778 direct calls against ceiling 6294. No ceiling was raised.
Raw scoped and canonical evidence is retained in build/smux-sosix-source-check.
These source findings do not close native qualification or release gates.
