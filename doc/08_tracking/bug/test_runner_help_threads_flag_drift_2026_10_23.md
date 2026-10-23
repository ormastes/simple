# Bug: `simple test --help` advertises `--threads, -j <N>` which the runner rejects

Date: 2026-10-23
Lane: test-runner CLI (seed-verified, sources at release/1.0.0 head 7385cc9b07e)

## Symptom

`simple test --help` prints:

```
--parallel, -p          Enable parallel execution
--threads, -j <N>       Set worker threads
--worker-memory-mb <N>  Aggregate parallel worker RSS admission budget in MiB
```

but every accepted-looking form fails at run start with
`Error: unknown option: --threads` (also: `--threads=40`, `-j 40`, in any
position relative to `--parallel` and the spec path):

```
$ simple test --parallel --threads 40 --worker-memory-mb 4096 --no-cover-check test/
[MEM] START: MemAvailable: ...
Error: unknown option: --threads
```

## Cause

Help/option drift. The implemented knob in
`src/lib/nogc_sync_mut/test_runner/test_runner_args.spl` is
`--max-workers=<N>` (feeds `proc_slot_configure_requested_workers` and
`gov.max_cpu_cores` in test_runner_async.spl); no `--threads`/`-j` parsing
exists anywhere in the test-runner arg table. The `--help` text for the
`test` subcommand lists options the parser does not implement.

## Workaround (do not normalize silently)

Use `--max-workers=<N>`:

```
simple test --parallel --max-workers=40 --worker-memory-mb 4096 --no-cover-check test/
```

## Fix direction

Either implement `--threads`/`-j` as aliases of `--max-workers` in
test_runner_args.spl, or correct the `--help` text to advertise
`--max-workers=<N>`. Help text and parser table should be generated from one
source to prevent recurrence.

## Repro

Any of:

```
build/seed-cargo-target/bootstrap/simple test --parallel --threads=40 test/00_quick
build/seed-cargo-target/bootstrap/simple test --parallel -j 40 test/00_quick
```
