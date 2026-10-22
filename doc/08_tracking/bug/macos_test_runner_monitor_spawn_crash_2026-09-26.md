# macOS test runner monitor spawn crash

Status: open. Severity: P1. Observed on macOS 26.5 on 2026-09-26.

The `simple` crash reports at 13:24:44, 13:43:16, and 14:46:14 local time
show `SIGSEGV` / `KERN_INVALID_ADDRESS`. The faulting stack includes
`_platform_memmove` → `rt_process_spawn_async` →
`ensure_kill_monitor_running` in
`src/lib/nogc_sync_mut/test_runner/system_monitor.spl` (around line 664).
The last function launches `sh scripts/resource/kill_simple_monitor.shs`.

The reports list 271–349 GB of **virtual** writable regions, but only 192 KB
resident in those regions at the crash snapshot. This is not evidence of
271–349 GB physical memory consumption. Current `memory_pressure` reported
88% system-wide memory free; a one-second `vm_stat` sample had zero pageouts
and zero swapouts. These observations support an invalid-access diagnosis,
not a confirmed out-of-memory kill.

The newer 15:54:34 `simple` crashes are separate `SIGBUS`/`SIGSEGV` faults in
the lint path with approximately 93 MB writable virtual regions. The earlier
focused spec's child exit remains inconclusive; its exact crash identity was
not established from these reports.

Next: reproduce with a bounded single monitor launch on an admitted
self-hosted binary, inspect the native `rt_process_spawn_async` argument ABI
and buffer lifetime, and add a regression test. Do not repeat the full suite
until this path is fixed. macOS process listing and unified logging are
unavailable inside the current sandbox.

Source mitigation added on 2026-09-26: both test-runner monitor modules now
launch this one macOS safeguard through the existing synchronous shell facade
with a detached `nohup sh` command and check that a positive PID was returned.
The shell form returned a PID in a local command probe. The Simple source path
has not run on a source-matched pure-Simple binary, so the crash is still open.
The underlying `rt_process_spawn_async` bug also remains open for other users.

The two owned C runtime variants now prepare argv in the parent and use
`posix_spawnp` on macOS; invalid argument counts and a missing argument array
are rejected before dereference. A focused self-check linked separately
against `runtime.c` and `runtime_legacy_core.c` passed on this macOS host:
real `/bin/sh` exit 7 while a second thread was live, null/negative/oversized
argument cases, and missing-executable rejection. The count cap is Apple-only;
null argument elements are rejected there too. Both translation units passed
Clang syntax checks. This is native boundary evidence only;
Simple codegen/FFI, the test runner, and the full distributed build still need
a fresh source-matched pure-Simple qualification pass. The bug remains open.
