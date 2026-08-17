# `simple replay` self-spawns an unbounded chain of `simple` processes (~8 GB/min host-wide)

- **ID:** simple_replay_self_spawns_unbounded_process_chain_2026-08-10
- **Status:** RESOLVED 2026-08-17 — spawn site located and fixed; regression
  specs landed. See "Resolution" at the bottom.
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

## Resolution (2026-08-17)

**Spawn site (the "not yet located" item):** `delegate_replay` in
`src/app/replay/main.spl`. Reached from `main()` for any non-`.srr` argument, it
unconditionally re-invoked `./bin/simple replay <same args>` as the "delegate to
the Rust CLI" fallback. The Rust seed's own `run_replay`
(`src/compiler_rust/driver/src/cli/audit.rs:222`) never spawns, and
`src/app/cli/bootstrap_check.spl:376` is only a command→source coverage table —
both were red herrings in the "What is known" section above. The seed dispatches
`replay` by interpreting `src/app/replay/main.spl`, so the child re-entered the
same `.spl` delegation and recursed. Same failure family as
`cli_compile_delegation_fork_bomb_wrapper_2026-07-24.md` and the
`is_release_wrapper_self_delegation` fix — a facade re-spawning the CLI already
running — but a *different* code path: `src/compiler/80.driver`'s
`check_compile_delegation_guard` was never on the replay route, so neither the
`SIMPLE_COMPILE_DELEGATED` marker nor the same-binary-path check could fire.

**Fix:** `cac573c5ecf3` ("fix(replay): stop unbounded self-spawn chain in
delegate_replay") removed the re-invocation. The failure path now checks the
file and returns, with no process spawn at all — a *stronger* fix than the depth
stamp asked for in "Next steps" item 2, and it satisfies item 4 directly
(fail fast, non-recursively, on a missing input file).

**Reproduction under a hard bound** (item 1), run 2026-08-17 from the repo root
against the deployed seed:

```
$ systemd-run --user --scope -q -p TasksMax=15 ./bin/simple replay /nonexistent-build-log.json
log file not found: /nonexistent-build-log.json
EXIT=1
```

Terminates immediately; the `TasksMax=15` scope was never approached, and the
host-wide `simple` process count did not grow. The same invocation through the
spec's own route (`bin/simple run src/app/replay/main.spl missing-build-log.json`)
gives `log file not found: missing-build-log.json`, exit 1.

**Regression guard** (item 3), landed 2026-08-17:

- `test/02_integration/app/replay_log_modes_spec.spl`
- `test/integration/app/replay_log_modes_spec.spl` (mirror, byte-identical)

Two `it` blocks: a reproducing scenario asserting the run terminates inside a
hard `timeout 120` bound (the defect's parent never returned — `timeout` would
report 124) and names the missing path; and a prevention scenario asserting the
old delegating wording `Failed to read log file` is absent, so any restored
fallback fails the spec before it can fork-bomb a host. The pre-existing
`it "delegates non-srr replay logs to the rust CLI"` had been left asserting the
*defective* behaviour and was silently red since `cac573c5ecf3`; it is replaced
by those two.
