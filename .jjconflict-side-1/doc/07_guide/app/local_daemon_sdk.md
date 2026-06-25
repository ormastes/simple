# Local Daemon SDK Guide

## Purpose

`std.daemon_sdk` is the reusable local daemon library. It provides one-server,
multi-client file IPC with a PID lock, request/response directories, and a
polling daemon runner.

## Health Contract

A live PID is not enough. Clients that need automatic recovery should call:

```simple
daemon_ensure_responsive(config, start_fn, ping_fn)
```

The helper starts the daemon if no lock owner exists. If a lock owner exists but
`ping_fn` fails, it terminates that owner, starts a replacement, and pings again.

## Idle Resource Use

Daemon implementations should choose idle and busy poll intervals explicitly.
The test runner daemon uses a longer idle interval and a shorter busy interval
through `app.test_daemon.resource_policy`.
