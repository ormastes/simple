# Light test daemon cannot serve a pinned native binary or exec mode

Status: OPEN (P3, deferred). Registered 2026-11-03.

The light daemon (src/app/test_daemon/light_daemon.spl) is pinned for life to
the binary that spawned it and its v2 request (light_protocol.spl) carries a
path, expiry, environment digest and generation, but no binary or execution
mode. The client therefore diverts to the direct lane for `--compiler`,
SIMPLE_* binary overrides, and a daemon binary differing from the invoker
(test_runner_client.spl: compiler_bypass, binary_override_bypass,
invoker_bypass). That is a correct fail-safe, but it means pinned native runs
never use the daemon. The session daemon already carries a native profile
(src/app/test_daemon/native_profile.spl, PR #5407).

On non-linux hosts the light daemon is bypassed entirely
(daemon_backlog.spl daemon_platform_bypass), so this cannot be exercised on
Windows.

Decision needed: keep the documented bypass, or add a native profile field to
the light v2 request and have the daemon refuse mismatches. Verify on linux.
