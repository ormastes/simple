# PostgreSQL mimic native daemon traps before bind

## Status

Open. Native-build admission passes, but the compiled daemon is not runnable.

## Evidence

- Compiler: `build/simpleos-enhance-current-stage2/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
- Compiler SHA-256: `84e60ed802e6fe49c7df015ff87fd58ac7fa40253c1e1833bc72757d59462`
- Artifact: `build/native_probe/postgres_mimic_admitted/postgres_mimic_server`
- Artifact SHA-256: `4c9036bbd8e4a40fe401fec64630f33987bd7a27b84de828fa347a4c3714b60a`
- Strict native gate: PASS (`1 compiled, 77 cached, 0 failed`)

## Reproduction

Run the artifact with:

```text
--serve --listen 127.0.0.1:55439 --allow-user local
--allow-database default --workers 1 --max-connections 1
```

Before a PostgreSQL v3 StartupMessage can connect, the process prints
`runtime error: invalid field receiver` and terminates with status 132
(`Illegal instruction`). The loopback client receives connection refused and
zero response bytes.

## Acceptance criteria

1. The same admitted native artifact reaches the listening state without a
   receiver trap.
2. One PostgreSQL v3 StartupMessage authenticates the allowed user/database.
3. `SELECT 1` returns a valid RowDescription/DataRow/CommandComplete/ReadyForQuery
   sequence.
4. A rejected user/database receives a PostgreSQL ErrorResponse without a
   process crash.

The command currently has no `--check` mode; invoking `--check` falls through
to query mode and exits 2 with `--query is required`.

## DFD3 retained-artifact diagnosis

The later retained artifact
`build/native_probe/postgres_mimic_dfd3_admitted/postgres_mimic_server`
exited with `postgres-mimic serve failed: -50889066035544064`. This number is
not a socket errno. Its retained `run_server` object masks the `Result` error
payload and loads the displayed value from payload offset `0x28`, while
`IoError` contains only three words and its `message` is the word at offset
`0x08`. The number is therefore an out-of-bounds heap word produced by an
incorrect imported enum-payload field layout.

The retained `serve_bounded` object shows that the early return is in the
first-listener loop: `TcpListener.bind_reuseport` returns `Err(IoError)`, that
payload is forwarded unchanged, and no worker-ready print is reached. The
backend has three failure points under that branch: socket creation,
`rt_io_tcp_bind_fd`, or `rt_io_tcp_listen`; the corrupt projection erased the
specific message, so this artifact cannot distinguish those sub-branches.

The app now formats the imported payload through `IoError.to_string()`, keeping
field projection in the type's defining module. This repairs diagnostics for a
new build; it does not claim to repair the underlying socket failure.

## Explicit-lambda acceptance

A fresh strict build with compiler SHA `dfd3c3b7...`, rooted Core-C runtime
archive SHA `7fbc95d6...`, and parallel-worker SHA `b805620c...` compiled 80/80
modules from an empty isolated cache. The worker used an explicit noncapturing
two-argument thread lambda.

Its sole daemon attempt still failed before readiness and TCP bind, now printing
`error: postgres-mimic serve failed: 0` and exiting 1. The only client received
`ECONNREFUSED`; Startup/query/Terminate and restart persistence were not
exercised. This disproves the thread-lambda representation as a sufficient fix
for the pre-bind failure and shows that `IoError.to_string()` still receives a
corrupt or incorrectly lowered imported `Result` payload at this call boundary.
See `build/mini_builds/db_lambda_acceptance_dfd3_20260812/acceptance.md`.

## Startup syscall trace

One `strace -ff -ttt -T` run of that exact artifact and the same daemon
arguments disproves the earlier "pre-bind" diagnosis. Both workers completed
`socket`, `SO_REUSEPORT`, `SO_REUSEADDR`, `bind(127.0.0.1:55441)`, and
`listen(..., 128)` successfully. Both `clone3` calls also succeeded. The main
thread wrote `postgres-mimic workers ready: 2`, but both worker threads closed
their respective listener and exited 0 without issuing `accept`/`accept4`.
The main thread then received `SIGSEGV` at address NULL 86 microseconds after
the readiness write. From process start to SIGSEGV was about 6 milliseconds;
core-dump handling made observed wall time 2.91 seconds and shell status 139.

The Core-C implementation of `rt_pg_parallel_worker_handoff_new` stores only
the original aggregate pointer in a scalar table. Contrary to its comment, it
does not register a root or retain the nested listener/control/dispatch
handles. The Rust runtime implementation wraps the aggregate in `rt_shared_new`,
so the two runtimes do not implement the same lifetime contract. The observed
immediate worker drain plus main-thread NULL dereference is consistent with
that Core-C lifetime defect. No source fix is claimed here: correcting it
requires a real Core-C ownership/root primitive, not another readiness delay.
Raw traces are `/mnt/data/db-lambda-acceptance-20260812/strace-startup-20260812.*`.
## Hosted inline acceptance update (2026-08-12)

An explicit hosted `--inline` profile removed thread and worker-handoff code
from the live path. A strict fresh artifact built 81/81 modules with runtime
capsule `dc231b80f9f93027b2f5e1565e1a5db30c743af45adfe2beb237e94cfb47eaf0`,
but still trapped before listener creation. GDB recorded `rdi=0x32`, masked to
`0x30`, at the guarded receiver load. This proves the admitted `dfd3c3b7...`
compiler mislowers an imported receiver independently of parallel execution.

The canonical compiler selector now builds **and runs** a two-module imported
class-method fixture and requires exact `imported=42` output. The `dfd3c3b7...`
compiler fails that gate and must not build further server evidence. A new
Stage2 must pass the receiver fixture and the external-library capability gate
before web or database acceptance resumes.
## Current Stage2 sanity reproduction (packed-memory-build3)

The current replacement bootstrap compiled a fresh Stage2 successfully
(`815 compiled, 0 cached, 0 failed`) but canonical sanity rejected it before
publication. Candidate SHA-256
`375319e7c5ffc5d9e452a3ff0906fee4ba4655d7a752cdb91f432379b00bc0b4`
exits status `132` for `--version` with `runtime error: invalid field receiver`.
The before/after binary hashes match, so this is a deterministic candidate
runtime/codegen failure rather than publication mutation. Evidence:
`/mnt/data/bs2/packed-memory-build3/stage3/x86_64-unknown-linux-gnu/stage2-sanity.env`
and `logs/x86_64-unknown-linux-gnu/stage2-native-build.log`.

This independently reproduces the same invalid-receiver class before either
server starts. The Stage2 artifact is diagnostic only and must not be used for
web, database, runtime-capsule, or performance acceptance.
