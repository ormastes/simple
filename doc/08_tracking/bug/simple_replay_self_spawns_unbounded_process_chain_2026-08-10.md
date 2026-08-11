# `simple replay` self-spawns an unbounded chain of `simple` processes (~8 GB/min host-wide)

- **ID:** simple_replay_self_spawns_unbounded_process_chain_2026-08-10
- **Status:** OPEN — mechanism measured, spawn site not yet located in source.
- **Severity:** critical (host-level). It exhausts a 128 GB host in minutes and,
  because `earlyoom` is configured with `--prefer '^(simple|...)'`, the
  resulting kills land on **unrelated, healthy `simple` processes** — Stage-3
  bootstrap builds, test runs, MCP servers — which then present as
  exit 143 with no diagnostic.
- **Found by:** the Q6 investigation of
  `stage3_frontend_hir_unbounded_memory_growth_2026-08-10.md`, whose entire
  reported symptom turned out to be this.

## Symptom

Hundreds to thousands of live processes, all with identical argv:

```
./bin/simple replay missing-build-log.json
```

Each is the **direct child of the previous one**, each ~62 MB RSS, and **every
ancestor stays alive** (`State: S`, blocked in wait). The chain root is orphaned
(`PPid 1`). Ancestry walk from the newest process:

```
2990142 ppid=2990025 :: ./bin/simple replay missing-build-log.json
2990025 ppid=2989909 :: ./bin/simple replay missing-build-log.json
2989909 ppid=2989800 :: ./bin/simple replay missing-build-log.json
2989800 ppid=2989658 :: ./bin/simple replay missing-build-log.json
```

## Measured growth (2026-08-10, 152 s window)

| t (s) | processes | aggregate `simple` RSS |
|---|---|---|
| 0 | 1101 | 67.6 GB |
| 60 | 1225 | 75.4 GB |
| 121 | 1349 | 85.0 GB |
| 152 | 1411 | 88.8 GB |

**~124 processes/min, ~8.4 GB/min, linear, no plateau.** Observed 952 → 1608 in
one session. `free -g` reached 97/125 GB used with 1 GB free.

Reproduce the measurement (read-only):

```sh
for i in 1 2 3; do
  echo "$(date +%s) $(ps -eo comm= | grep -c '^simple$')"
  sleep 30
done
```

## Collateral: earlyoom kills the wrong process

```
Aug 10 07:28:03 dl earlyoom[1479]: mem avail: 11988 of 128683 MiB ( 9.32%) ...
Aug 10 07:28:03 dl earlyoom[1479]: sending SIGTERM to process 2614312 uid 1000 "simple": badness 966, VmRSS 61 MiB
```

earlyoom matches by process **name**, so a healthy 270 MB Stage-3 build is an
equally-preferred victim of pressure created entirely by this chain. That is how
a non-leaking build acquires the signature "exit 143, no verdict line, RSS was
climbing at ~1 GB/min" — the RSS was the host's, not the build's.

## What is known about the mechanism

- The argument file does not exist: `missing-build-log.json` is absent from the
  repo root. So this is the **failure** path, not the success path.
- The handler itself cannot be the spawner: `cli_replay`
  (`src/app/io/_CliCommands/handler_commands.spl:236`) only prints
  `[experimental] Replay tool is not yet implemented` and returns 1. It performs
  no process spawn.
- Dispatch reaches it at `src/app/cli/_CliMain/main_and_help.spl:395-396`;
  `replay` is a registered command (`src/app/cli/dispatch/table.spl:308`,
  `src/app/cli/surface_alignment.spl:98`, and
  `src/app/cli/bootstrap_check.spl:376` maps it to `src/app/replay/main.spl`).
- Therefore the re-spawn happens **before or around dispatch**, in the launcher
  layer that re-executes a child `simple` (the same delegation family already
  documented for `simple test` delegating to a seed child). The deployed
  `bin/simple` on this host is the Rust seed, so the responsible code is most
  likely the seed's delegation path, not the `.spl` handler — **confirm before
  fixing, and fix in `.spl` if the pure-Simple driver shares the defect.**

## Next steps

1. Reproduce in isolation with a hard bound, e.g.
   `systemd-run --user --scope -p TasksMax=20 ./bin/simple replay /nonexistent.json`,
   and capture the ancestry with `ps -eo pid=,ppid=,args=`.
2. Locate the re-exec/spawn site in the launcher/delegation path and make
   delegation **non-recursive**: a delegated child must be marked (env stamp)
   so it can never delegate again. A depth stamp is the minimum fix; refusing to
   delegate a command the child also cannot handle is the correct one.
3. Add a regression guard that runs a known-unhandled subcommand under a
   `TasksMax` scope and asserts the process count never exceeds a small bound.
4. Independently: `simple replay` should fail fast and non-recursively on a
   missing input file rather than entering any delegation path at all.

## Immediate mitigation

Kill the chain root (it is orphaned; `PPid 1`), which reaps the whole chain:

```sh
ps -eo pid=,ppid=,args= | awk '$3 ~ /simple$/ && $2 == 1'   # identify first
kill -TERM <root-pid>
```

Do **not** use `pkill -f simple` — it self-matches and takes down unrelated
builds and tooling.
