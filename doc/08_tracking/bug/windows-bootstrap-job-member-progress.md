# Windows bootstrap progress omits orphaned Job Object members

The Windows Stage2 build on release_phase3 commit
33d5617950321ff8a10bbaecdfdc176cdd3fc59f exposed a progress telemetry gap.
The watcher reported roughly 82 MiB and 0.3 seconds of tree CPU while native
compiler PID 12856 had roughly 1.1 GiB RSS and hundreds of CPU seconds.
Both native ancestry and MSYS ancestry had lost the compiler's exec edge.
The compiler remained owned by supervisor PID 8968's named Windows Job Object.

The observer now queries the read-only membership of each reachable
bootstrap-session-exec.exe --supervise Job Object. It attaches job roots to
their supervisor and preserves ancestry inside the job. Watcher subtrees and
unrelated jobs remain excluded. An unavailable query, oversized list, missing
member, or member older than its supervisor rejects the whole sample instead
of publishing an apparently smaller, idle tree. Resource enforcement is unchanged.

Validation: 21 deterministic observer checks passed, as did the existing
Windows native-child/page-unit watcher fixture. A read-only sample of the live
bootstrap included PID 12856 with 529664 KiB RSS and 1631.765625 CPU seconds.
This verifies telemetry only; it does not qualify the resulting compiler.
