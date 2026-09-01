# Bug: Runaway `simple` process OOMs the whole host (session crash)

- **Date:** 2026-06-14
- **Severity:** P1 (takes down the entire machine / agent session)
- **Category:** memory (NOT storage)

## Symptom
The previous codex/claude session "crashed." Root cause is **memory exhaustion
(OOM)**, not disk.

## Evidence (kernel log, `dl`, 2026-06-14 04:36–05:32)
Repeated global OOM kills, all victims are `simple` (one `rustc`):

| time  | pid     | anon-rss   | total-vm   |
|-------|---------|-----------|-----------|
| 04:36 | 3523685 | ~117 GB   | ~112 GB   |
| 05:27 | 3796103 | ~92 GB    | ~94 GB    |
| 05:29 | 3806722 | ~45 GB    | ~45 GB    |
| 05:30 | 3806715 | ~65 GB    | ~66 GB    |
| 05:32 | 3808742 | ~118 GB   | ~119 GB   |

- Host RAM: 125 GiB + 8 GiB swap. A single `simple` reached ~117 GB anon-rss
  → `global_oom, constraint=CONSTRAINT_NONE`.
- The `simple` processes ran inside docker scopes
  (`task_memcg=/system.slice/docker-….scope`) that had **no memory limit**, so
  they competed for global host RAM and starved everything.
- **Not disk:** `/` is at 83% with 642 GB free; inodes fine.
- **The session was not itself OOM-killed** — only `simple` (and one `rustc`)
  were killed. The session died in the fallout of the host running out of RAM.
- No GC in Simple runtime ("allocate-and-leak", see memory audit) → a runaway
  compile/interp loop grows unbounded until OOM.

## Two distinct problems
1. **Containment (recurrence prevention):** docker containers that run `simple`
   have no `--memory` cap. The repo convention already exists —
   `scripts/check/check-cross-language-perf.shs:138` uses `--memory=2g`. Other
   `simple`-running containers should do the same, OR a host OOM guard
   (systemd-oomd / earlyoom) should fire before the host is starved.
2. **Root leak (open-ended):** the actual `simple` process grew to ~117 GB.
   Which input/loop triggers it is unknown and is a separate runtime bug to
   hunt. A memory cap prevents the host crash regardless of which leak fires.

## Pinpointed source (containment)
The uncapped containers were created by the **test daemon** container adapter,
`src/app/test_daemon/adapters/container_adapter.spl`:
- `start()` (was line 115) and `reset()` RESET_RECREATE (was line 194) ran
  `docker create … sleep infinity` with **no `--memory`/`--cpus`/`--pids-limit`**,
  then `docker exec`'d `bin/simple test` inside. A leaking `simple` there had no
  cgroup cap → grew to ~117 GB → `global_oom`.
- For contrast, the already-capped paths were fine: `docker_runner.spl`
  (`--memory=1g/4g/2g`) and `scripts/check/check-cross-language-perf.shs`
  (`--memory=2g`).

## Fix applied (containment) — 2026-06-14
`container_adapter.spl` now carries a `resource_flags` field
(`--memory=4g --memory-swap=4g --pids-limit=512 --cpus=4.0`) injected into both
`docker create` commands. `--memory-swap == --memory` disables swap so a runaway
is killed at the 4 GB cap instead of thrashing host swap into a global OOM.

## Remaining work
- **Host OOM guard (optional, defence-in-depth):** `systemd-oomd` is not present;
  install `earlyoom` (`sudo apt install earlyoom`) so no single process can take
  the box + agent session down even outside a container.
- **Root leak (open):** the `simple` process itself grew to ~117 GB. Simple has
  no GC ("allocate-and-leak"); a long `bin/simple test` run inside one process
  accumulates unboundedly. Hunt which spec/input balloons and add per-spec
  reclamation or process isolation. Tracked separately — the cap above prevents
  the host crash regardless of which leak fires.
