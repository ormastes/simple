# Windows managed RAW native negative fixture

Status: **NOT_RUN**. No Windows host is available in this source session.
Source: `test/03_system/app/orchestrator/feature/windows_managed_stream_cleanup_v2_spec.spl`.

The Windows-only fixture requires an unnested test process with one observed
processor group and an administrator-controlled `C:\SimpleQualification`
directory whose `absent-managed-stream-producer.exe` does not exist. It invokes
the actual managed owner, checks the returned cleanup lease, observes confirmed
no-child/no-Job membership, refuses a forged generation, then collects native
resources and refuses use after close. A second case rejects TTY mode before
native launch ownership is acquired.

This negative fixture does not qualify successful process creation, Job CPU or
memory enforcement, stream backpressure, native fault injection, Docker, or
interactive operation. Those Windows qualification gates remain outstanding.

`src/runtime/test/rt_windows_pty_owner_thread_selfcheck.c` is an additional
**NOT_RUN** Windows fixture. Two actual threads race the production owner guard;
exactly one may bind. It checks that the main thread is rejected while the owner
is alive and that owner exit prevents rebinding. This fixture covers the guard,
not the complete Simple registry or Job/stream behavior.
