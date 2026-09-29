# PostgreSQL Mimic Parallel Live Probe — 2026-08-11

Status: **RED (bootstrap interpreter is not a worker-runtime oracle).**

## Scope

The probe launched `postgres_mimic_server serve` on `127.0.0.1:55439` with
`--workers 2 --max-connections 2`. Client 1 was intended to remain open after
startup while client 2 completed startup and `VALUES (2)`.

## Evidence

- The production entry closure parsed after `PgWireLinuxLimits` was extracted
  from the obsolete serial adapter.
- The daemon created both listening sockets and printed its startup line.
- A TCP client connected, but PostgreSQL startup received no response before a
  five-second deadline.
- The available tool identified itself as the Rust bootstrap seed, rejected the
  Cranelift closure ABI, and fell back to the interpreter.
- Earlier in the same probe the interpreter lacked `spl_mutex_create`; after
  moving lifecycle counters to the canonical no-GC mutex, native worker entry
  still made no observable progress.

This does not prove a pgwire protocol failure: the socket-neutral dispatcher
spec retains two distinct client jobs and the TCP listener accepted a connect.
It also does not prove concurrency. A release-native executable with functioning
`spl_thread_create` remains mandatory.

## Fail-fast improvement

The server now requires every spawned worker to increment a protected ready
counter within five seconds. A zero thread handle or missing ready transition
returns a typed startup error instead of leaving a listening but inert daemon.

The audit also found that the first worker implementation called raw
`spl_thread_create`, whose C owner accepts `void *(*)(void *)`, with a Simple
closure/function value. That ABI is invalid. The server now uses the canonical
`thread_spawn_with_args` owner with an explicit slot argument and `ThreadHandle`
cleanup. The in-repo native ABI smoke for that owner reports PASS; pgwire still
requires its own release-native live rerun.

## Next acceptance run

Use an admitted pure-Simple native compiler/runtime. Require two worker-ready
receipts, then retain client 1 while client 2 completes startup/query. Preserve
the raw server transcript, client transcript, executable SHA-256, compiler
receipt, latency, CPU, and maximum RSS. Only that result may promote this test.
