
## The two Stage-3 blockers are INTERLOCKED (2026-09-02)

Stage 3 currently has two independent blockers, and they obstruct each other:

1. **E-MIR-TYPE-ZeroKind** — an ABI dead-copy defect
   (`zerokind_roams_between_victims_avoidance_edits_are_not_fixes_2026-09-02.md`).
   Six runs, five refuted hypotheses, count immovable at 2. Diagnosing it requires
   the two-sided tag probe, which fires during **MIR function lowering**.
2. **This record** — the host kills Stage 3 with signal 127 during
   **phase4:monomorphize**, which runs *before* MIR function lowering.

So on a memory-constrained host the run dies **before the probe can fire**. Measured
directly: the instrumented run reported `probe lines: 0` alongside
`KILLED by signal 127`. The instrument is correct and in place; it simply never
executes.

**Consequence for whoever picks this up:** resolve the memory blocker FIRST. Any
attempt to diagnose ZeroKind on a host in this state produces no evidence and costs
~55 minutes per attempt. The ordering is not optional.

Levers tried against the memory blocker, and why each failed:

| lever | result |
|---|---|
| `SIMPLE_NATIVE_BUILD_THREADS=1` (honoured, BFS:1024) | steady-state RSS 4.6 GB -> ~420 MB; **peak unchanged** — the monomorphize peak is one single-threaded allocation, not parallel workers |
| compiler low-memory path | **unavailable**: gated on `SIMPLE_BOOTSTRAP=1 AND SIMPLE_BOOTSTRAP_STAGE4=1 AND SIMPLE_BOOTSTRAP_LOW_MEMORY=1` (`bootstrap_low_memory_config.spl:11`); forcing `STAGE4=1` changes Stage-3 semantics (`driver_aot_pipeline.spl:62-65`) |
| `purge` | requires root on this host |
| reaping stale repo processes | they are 0.6-4 MB each; no material gain |
| `SIMPLE_MEM_ARENA_DELAY_SLOTS` | wrong subsystem — AST-arena stale-read hardening, not an allocator bound |

What is left is not a software lever: free RAM. The host has 24 GB with ~9.3 GB of
10.2 GB swap committed after ~30 days of uptime, and the peak need is ~4.5 GB. A
reboot, or a machine with headroom, is sufficient — **the compile itself is clean
(HIR 760/760, 0 fatals), so nothing in the repo needs to change for a larger host to
get further.**
