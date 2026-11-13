# Windows memory-headroom gate false-refuses on ballooned VMs (AvailPhys under-reports)

Date: 2026-11-13
Branch: work/headroom-balloon-refusal (base origin/release/1.0.0 @ 48a03dc9e2b)
Host: DESKTOP-VMF96U6 (Hyper-V dynamic-memory guest), 64 GiB visible RAM, Windows 11

## Symptom

Stage-2 MSVC bootstrap (cycle 7, release/1.0.0 @ 85b7efbd9e6) compiled all 1648
modules and linked the candidate `simple.exe`, then the post-link sanity refused:

```
Stage 2: running bootstrap compiler sanity
error: sanity FAIL - frontend smoke exited 3 (bootstrap-mode pass: 0)
error: build refused: 3717 MiB of RAM/commit headroom free, below the 24576 MiB
reserve (SIMPLE_BUILD_MEMORY_RESERVE_BYTES); wait for other builds to finish or
lower the reserve
candidate_frontend_smoke: scv_prime left no source inventory in build/scv (raw rc=3)
```

The refusal came from the stage2 candidate itself running `check --help` (the
scv-prime step in scripts/bootstrap/bootstrap-scv-prime.shs).

## Measurement chain

- `build_memory_start_refusal_v1` (src/app/cli/shard_mem_clamp.spl:813-818):
  refuses when `available_kib < reserve_kib`. Called from
  src/app/cli/native_build_main.spl at native-build start.
- `available_kib`: `shard_mem_available_kb` (shard_mem_clamp.spl:30-33) ->
  `windows_available_memory_headroom_v1` ->
  `rt_host_memory_headroom_bytes_v1` (src/runtime/runtime_memory_headroom.c:11-22)
  = `min(GlobalMemoryStatusEx.ullAvailPhys, ullAvailPageFile)`.
- `reserve_kib`: `SIMPLE_BUILD_MEMORY_RESERVE_BYTES` env, else host config
  `mem_reserve_free_mib`, else `min(24 GiB, installed RAM / 2)`
  (shard_mem_clamp.spl:767-809). On this 64 GiB host the default is 24 GiB.
  Introduced by 5b9b780b8a3 after a ~127 GiB host filled under concurrent builds.

## Why the measurement lies here

At the refusal moment the host showed (PowerShell/CIM, perf counters):

- `Win32_OperatingSystem.FreePhysicalMemory` = 3.6 GiB (matches the gate's 3717 MiB)
- `\Memory\Committed Bytes` = 17.6 GiB of a 69.5 GiB commit limit
- Sum of ALL 207 processes: WorkingSet 11.1 GiB, Private 8.9 GiB; largest
  single process svchost at 4.9 GiB
- ~45 GiB of physical RAM attributable to no process — classic Hyper-V
  dynamic-memory balloon: the host reclaims guest pages (they leave the
  free/standby/zeroed lists GlobalMemoryStatusEx counts), and returns them on
  demand when the guest allocates.

Definitive in-guest proof that the gate's number is phantom:

```powershell
# 6 x 1 GiB AllocHGlobal, one byte touched per 64 KiB page:
allocatedGB=6 ... ALLOC-6GB-OK elapsed=0.5s
# and 24 x 1 GiB:
allocatedGB=24 failedAt=0 freeAfterGB=3.1 elapsed=0.8s
```

24 GiB of demand is satisfied in under a second while `ullAvailPhys` reports
~3.7 GiB. The first 6 GiB probe actually RAISED FreePhysicalMemory 3.4 -> 7.6 GiB
(balloon deflation side effect). There is no in-guest API that exposes balloon
state, so the min(AvailPhys, AvailPageFile) metric cannot distinguish
"genuinely exhausted" from "balloon-inflated but deliverable" on such hosts.

Note this is the same class of surprise the user asked about ("windows memory
use api call then not cleaned"): no process leak — the RAM sits outside process
accounting. Related retention concern (seed parent ~28 MiB/module in-driver) is
tracked separately in bootstrap_stage2_seed_parent_retention_oom_2026-10-22.md.

## Mitigation (applied, unblocks the lane)

Set the reserve below the phantom reading for the bootstrap invocation:

```
SIMPLE_BUILD_MEMORY_RESERVE_BYTES=1073741824   # 1 GiB
sh scripts/bootstrap/bootstrap-windows.sh --msvc --full-bootstrap ... 
```

This is the documented escape hatch in the refusal text itself. Risk on THIS
host: none demonstrated — 24 GiB allocations succeed instantly and the live
RSS guard still gates each worker spawn during the build
(shard_mem_clamp.spl:743-750). At tip 48a03dc9e2b the knob no longer voids the
native module cache identity either (#8920,
3da9e9e1c7d), so a retuned reserve does not force a cold rebuild.

Longer-lived alternative for a permanently-ballooned host: set
`mem_reserve_free_mib` in the machine host config so every invocation inherits
it without env plumbing (build_memory_reserve_kib, shard_mem_clamp.spl:801-809).

## Candidate fix directions (deferred to design — NOT implemented)

Any change touches safety policy that 5b9b780b8a3 added after a real fill-up
incident, so none of these should land without repro across host types:

1. **Commit-witness fallback**: when `min(AvailPhys, AvailPageFile) < reserve`
   but `ullAvailPageFile >= reserve` AND installed RAM >= 2 x reserve, admit
   with a warning (commit headroom can absorb the reserve; the OS satisfies
   physical demand via balloon deflate / cache trim). Weakness: admits on
   genuinely RAM-tight-but-huge-pagefile machines (thrash, not OOM; the spawn
   RSS guard still applies).
2. **Probe-on-refusal**: when refusal is imminent, attempt one bounded private
   allocation (e.g. min(reserve - available, 1 GiB)); success -> admit with
   warning. Weakness: doubles as an accidental memory stress test on genuinely
   tight hosts; needs a strict timeout.
3. **Balloon-aware Windows provider**: replace GlobalMemoryStatusEx with
   GetPerformanceInfo + an explicit balloon estimate. There is no supported
   in-guest balloon counter, so this is likely a dead end.
4. **Status quo + host-config detection**: keep the gate, ship a bootstrap-host
   capacity probe (scripts/bootstrap/bootstrap-host-capacity.shs already reads
   CIM) that writes mem_reserve_free_mib when it detects the balloon pattern.

## Verification of the diagnosis

- Gate location and reserve chain: read directly at tip 48a03dc9e2b
  (shard_mem_clamp.spl:30-33, :767-818; runtime_memory_headroom.c:11-22;
  windows_process_owner_abi.spl:18-26).
- Phantom-memory proof: the two PowerShell AllocHGlobal probes above (6 GiB and
  24 GiB, page-touched, sub-second), plus the process-sum accounting showing
  11.1 GiB of 63.8 GiB attributable to processes.
- Mitigation evidence: cycle-8 stage2 bootstrap at 48a03dc9e2b with
  SIMPLE_BUILD_MEMORY_RESERVE_BYTES=1073741824 — see
  build/mcp-stage2-bootstrap-tip48a0.log in the bootstrap worktree.

## Residual risk

- The 24 GiB default reserve on >= 48 GiB hosts makes every `simple check`
  admission on a ballooned VM depend on the phantom reading; users on Hyper-V
  dynamic-memory guests (common for dev VMs) will hit this after ANY memory-
  intensive workload inflates the balloon. Mitigation knowledge (env knob /
  host config) must be discoverable — currently only the refusal text mentions
  it.
- CI runners are usually non-dynamic VMs, so this is unlikely to bite CI, which
  also means the project's own lanes are unlikely to rediscover it.
