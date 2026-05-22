# DBFS Integration — Risk Pre-Mortem

**Feature:** `dbfs-integration`
**Phase:** 5 (parallel, this doc is risk-side artifact)
**Date:** 2026-04-28
**Author:** Risk pre-mortem agent (Claude Opus 4.7 1M)
**Scope:** Imagine ship-day + 90 days. For each of the 13 risks, write the
production incident, the gap that let it through, the earliest detectable
signal, and a counter-mitigation that fits within the 10 ACs.

## Risk-set reconciliation

The user prompt enumerates 13 risks (R1–R13). The architecture doc's `D12. Risk
Register` also enumerates 13 (also numbered R1–R13) but with a different cut.
Reconciliation:

| Prompt# | Prompt name | Arch D12 # | Notes |
|---|---|---|---|
| R1  | Intent-log disk persistence (HIGH)             | R1  | Same. |
| R2  | Checkpoint-ring disk persistence (HIGH)        | R2  | Same. |
| R3  | Double journaling (DB WAL + FS journal + FTL)  | R3  | Same. |
| R4  | Double cache (DB cache vs kernel page cache)   | R4  | Same. |
| R5  | Large-file random-overwrite page churn         | R5  | Arch frames as COW amplification. Same scenario. |
| R6  | Scope creep (mmap shared-write, hard links, holes, O_DIRECT) | R12 | Arch numbers it R12; prompt numbers it R6. |
| R7  | Recovery bugs (committed-vs-uncommitted ambiguity) | (partial R9) | Arch R9 is *orphan reclamation*, not commit-boundary ambiguity. Treated as a distinct risk per prompt; cite D5 step 3 rule. |
| R8  | jj submodule gitlink flip                      | R10 | Same memory feedback (`feedback_jj_submodule_gitlinks`). |
| R9  | Submodule race with parallel /dev              | R13 | Same memory feedback (`feedback_submodule_race_parallel_dev`). |
| R10 | Extern bootstrap rebuild missed                | R11 | Same memory feedback (`feedback_extern_bootstrap_rebuild`). |
| R11 | Compile-mode false-greens                      | **(absent)** | D11 only mentions "interpreter-mode only" as a constraint; never registered as a risk in D12. |
| R12 | jj clobbers uncommitted Edit-tool changes      | **(absent)** | Different memory feedback (`feedback_jj_uncommitted_clobbered_by_parallel`); arch R10 covers gitlink flips, not Edit-tool drops. |
| R13 | BlobBackend conformance suite missing a variant | **(absent)** | Arch D6 collapses BlobBackend to the existing `Arena` trait with two impls (`RawNvmeArena` + NVFS Arena), but no shared-conformance-suite risk recorded. |

**Coverage policy:** All 13 prompt risks covered. The three risks
absent from D12 (R11/R12/R13) are explicitly the strongest pre-mortem candidates
because a risk never registered is by definition the one with the weakest
mitigation.

---

## R1 — Intent-log disk persistence (HIGH)

**Failure scenario.** Ship-day + 6 weeks. A user runs the photo-reel app from
the Instagram-style UX inlined in the user request: ~300 reels uploaded over
WiFi with the device unplugged. Battery dies mid-upload. On the next boot,
DBFS mounts cleanly, fsck reports no errors, but ~47 reels show as zero-byte
files in `/data/reels/`. Cause: `wal_append` returned success while the intent
log entry was still in a buffered page in `DB_WAL` arena memory; only the data
blobs hit disk via `arena_append`. The `COMMIT` records were lost. Per D5 step
3, those txns are correctly classified uncommitted — but the user expected
durable behavior because the upload UI showed "saved".

**Why mitigation didn't catch it.** Spec `dbfs_engine_wal_spec.spl` verifies
LSN monotonicity, CRC32C, append correctness — but in interpreter mode, the
"durable" flush is a no-op stub. Spec is satisfied without exercising actual
disk barrier semantics. `dbfs_engine_intent_log_spec.spl` and
`power_cut_harness.spl` test the in-memory ring; the disk-persistence assertion
is implicit.

**Earliest detectable signal.** Phase 7 bench `append_log_bench.spl` would
show throughput equivalent to no-flush (megabytes per second much higher than
the SSD's sync-write ceiling). A throughput value > 80% of memcpy speed should
fail the bench. Currently no such ceiling assertion exists.

**Counter-mitigation (fits AC-5/AC-9).** Add to `dbfs_engine_wal_spec.spl` and
`power_cut_harness.spl`: an explicit invariant test that after `wal_append`
returns `Ok`, killing the harness and re-reading the underlying arena yields
the appended bytes byte-for-byte. Use a fault-injection arena that records
`flush()` calls and asserts `flush()` count ≥ commit count. No new AC needed —
strengthens AC-5.

---

## R2 — Checkpoint-ring disk persistence (HIGH)

**Failure scenario.** Ship-day + 3 weeks. A QA build with debug logging crashes
the test machine 200 times via fault injection. On crash 173, mount fails with
`EIO: no clean checkpoint found`. The disk is fine; the latest checkpoint
entry was scheduled to write to META_DURABLE but the call returned `Ok` from
the in-memory ring before `arena_append` flushed. Recovery scans the ring and
finds zero `clean=true` entries (all 4096 slots stale).

**Why mitigation didn't catch it.** `dbfs_engine_checkpoint_ring_spec.spl` and
`dbfs_recovery_spec.spl` exercise ring-replay logic but assume the ring is
correctly written. The architectural mitigation (R2 in arch D12: "CheckpointEntry
written to META_DURABLE before clean=true") is a *protocol* — and protocols
fail when one author misreads the ordering. There's no spec that
counter-injects an out-of-order publish.

**Earliest detectable signal.** A reproducible failure in `power_cut_harness`
when fault threshold is set to "after first checkpoint write but before
META_DURABLE flush". Without that exact threshold, the bug hides.

**Counter-mitigation (fits AC-5).** Extend `power_cut_harness.spl` with a
fault-injection mode that requires the harness to model "fault between
checkpoint-publish and arena-flush" as a discrete state, not a probabilistic
sample. Add invariant: post-recovery `clean_checkpoint_gen ≤ flushed_arena_gen`
asserted in `dbfs_recovery_spec.spl`.

---

## R3 — Double journaling (DB WAL + FS journal + FTL)

**Failure scenario.** Ship-day + 8 weeks. A telemetry team enables
DBFS-on-NVMe-on-LUKS-on-ext4 (yes, sandwiched — they didn't read AC-7's
intent). Their write amplification jumps to 7.4×. SSD warranty wear-hours
projection drops from 5 years to 8 months. Worse: per-record fsync pattern in
WAL writes (because `DURABLE_GROUP_COMMIT` was implemented as "flush every
record" in the kernel-linked branch by mistake) interacts catastrophically
with FTL GC.

**Why mitigation didn't catch it.** Arch R3 says "Use DURABLE_GROUP_COMMIT
(one flush per commit, not per record); document in AC-10." But "one flush per
commit" is still not enough when commits-per-second is high. No spec asserts a
*minimum* batch size or a *maximum* fsync rate. AC-10 documentation is not a
runtime guard. `bench_harness.spl` measures throughput but not flush count.

**Earliest detectable signal.** A flush-count regression test in
`append_log_bench_smoke_spec` would catch this — assert
`flush_count ≤ commit_count` AND
`flush_count ≤ wall_time_seconds × MAX_FLUSH_HZ` (e.g., 200 Hz cap).

**Counter-mitigation (fits AC-9).** Extend `bench_harness_smoke_spec.spl`
with a "fsync rate ceiling" assertion. Add a sentinel hook in
`arena_append(durability=DURABLE_GROUP_COMMIT)` that increments a per-mount
counter; the bench harness reads it before/after the run.

---

## R4 — Double cache (DBFS buffer manager + kernel page cache)

**Failure scenario.** Ship-day + 10 weeks. A user reports `/data` performance
2× slower than `/legacy` (FAT32). Investigation shows: the kernel-linked DBFS
build ended up routing INODE/DENTRY page reads through `kernel_page_cache_get`
because a well-meaning kernel-side patch added "transparent caching" to
`BlockDevice.read_sector`. Now every metadata page lives in two caches —
DbFsBufferManager (keyed `(ino_id, page_id)`) and the kernel page cache
(keyed `(device_id, lba)`) — and writes invalidate the wrong one half the
time.

**Why mitigation didn't catch it.** Arch R4 mitigation: "verified in Phase 7"
— but the actual verification is documented as a manual call-graph review, not
an automated test. `dbfs_hw_passthrough_spec.spl` exercises `open_on_device`
but doesn't enforce that DBFS reads bypass the kernel page cache.

**Earliest detectable signal.** A counter-based assertion: after a
DBFS metadata-heavy workload, `kernel_page_cache.entries_for(dbfs_device).len()
== 0`. Currently no such counter is queried.

**Counter-mitigation (fits AC-3/AC-9).** Add `dbfs_kernel_cache_isolation_spec.spl`
(or extend `dbfs_hw_passthrough_spec.spl`) with one `it`: after running 1000
DBFS metadata ops, assert the kernel page cache has zero entries with
`device_id == dbfs_device.id`. This is an invariant that codifies the
"convention" mitigation as a runtime check.

---

## R5 — Large-file random-overwrite page churn (COW amplification)

**Failure scenario.** Ship-day + 4 weeks. A video-edit app does scrubbing on a
2 GiB MP4 in `/data/projects/`. Each 4 KiB random overwrite triggers: new
EXTENT allocation, EXTENT_REF rewrite, FILE_VERSION row insert, B-tree leaf
COW, and a 200-byte WAL record. Per-write disk amplification: ~32 KiB written
to disk for each 4 KiB user write. After 30 minutes of editing, the device's
SLC cache is exhausted, write latency spikes from 1 ms to 80 ms, and the app
visibly stalls.

**Why mitigation didn't catch it.** Arch R5 mitigation: "extent coalescing in
vacuum pass; benchmarked in `random_overwrite_bench.spl`." Vacuum is a
follow-up; bench reports a number but has no assertion threshold. AC-9 says
"benchmark harness covering random-overwrite large file" — covering is not
asserting.

**Earliest detectable signal.** A regression threshold in
`random_overwrite_bench_smoke_spec` — e.g., assert IOPS ≥ 5000 on a 1 GiB
file, or assert disk-write-amplification ≤ 8×. Currently no threshold.

**Counter-mitigation (fits AC-9).** Add to `bench_harness_smoke_spec.spl`: an
explicit write-amp ceiling for random-overwrite workload, even if the
threshold is generous (16×). At least one numeric guardrail. Document the
threshold in `dbfs_architecture.md` so regressions are visible.

---

## R6 — Scope creep (mmap shared-write, hard links, holes, O_DIRECT)

**Failure scenario.** Ship-day + 7 weeks. A community contributor opens a PR
adding `mmap(MAP_SHARED + PROT_WRITE)` "for free" — they noticed the buffer
manager already exposes pages and wired up a syscall path. Review approves it
because no one re-checks the arch out-of-scope list. Two weeks later, a
production user hits a kernel panic when an mmap region is written
concurrently with a `unlink` of the underlying inode. The COW path has no
visibility into mapped pages; recycled physical frames get written into stale
mappings.

**Why mitigation didn't catch it.** Arch R12 (= prompt R6) mitigation:
"Explicitly out of scope per Phase 1 decisions; out-of-scope list locked in
D10." But D10 is documentation. There's no spec or build guard that *fails* if
out-of-scope APIs are exposed.

**Earliest detectable signal.** A negative spec — e.g., "DbFsDriver does NOT
expose mmap_shared". `dbfs_capability_spec.spl` already corrected itself
(post-advisor review) to assert `caps.has(Dedup).to_equal(false)`. Extending
that pattern to all out-of-scope APIs would catch this.

**Counter-mitigation (fits AC-8).** Extend `dbfs_capability_spec.spl` with
explicit negative assertions for all 6 out-of-scope ops in D10
(`MmapSharedWritable`, hard links, hole-punch, O_DIRECT, per-file fsync, flock).
For the 5 not in the Capability enum today, add a `not_supported_ops()` -> `[String]`
method on DbFsDriver and assert each name appears.

---

## R7 — Recovery bugs (committed-vs-uncommitted ambiguity)

**Failure scenario.** Ship-day + 5 weeks. An NVMe link reset mid-write tears
the WAL tail: the data-block writes for txn 9001 completed, but the
subsequent COMMIT record only partially landed — the disk now contains a
prefix that happens to be a valid *earlier* record shape (different record
type, different txn_id) because record framing is fixed-position and the
trailing bytes weren't overwritten. Recovery (D5 step 3) walks the WAL,
re-frames the partial bytes as a complete prior-style record, and either
treats txn 9001 as committed when it wasn't, or skips it incorrectly when it
was. Replay produces a B-tree that references EXTENT rows pointing at
uninitialized arena regions. The B-tree now references EXTENT rows pointing at uninitialized arena
regions. Reads return zeros (silent corruption) for files that should have
been rolled back.

**Why mitigation didn't catch it.** Arch R9 covers *orphan* reclamation
(extra arenas, idempotent discard) but not *false-positive* COMMIT
recognition. D5 step 3 says "if record_type == COMMIT and TXN.status confirms
committed" — but TXN.status lives in the same WAL stream. There's no
independent check (e.g., committed-tx bitmap in META_DURABLE).
`dbfs_recovery_spec.spl` has `crash-then-recover` and `orphan reclaim` cases
but not `torn COMMIT record`.

**Earliest detectable signal.** A torn-write fault injection in
`power_cut_harness.spl` where the last N bytes of the COMMIT record are
overwritten with zeros after the data-block write completes. Run 100 seeds;
recovery should classify all as uncommitted. Currently the harness only
truncates at write boundaries.

**Counter-mitigation (fits AC-5).** Add to `dbfs_recovery_spec.spl`: a
`torn_commit_record` fault mode in the harness — overwrite arbitrary byte
ranges of the WAL tail and assert recovery never produces visible data from
those txns. Also add an invariant: every COMMIT record's CRC32C is computed
over `(record_body + txn_id + lsn)`, not body alone, so torn tails change CRC
input.

---

## R8 — jj submodule gitlink flip (per memory)

**Failure scenario.** Ship-day - 2 days (during Phase 8). A reviewer runs
`jj git push` after the parallel Phase 5 agent finishes. The push lands but
the next CI run fails with "submodule examples/simple_db is missing". jj
re-snapshotted the gitlink as a 040000 tree on its last reconcile (per
`feedback_jj_submodule_gitlinks`). The DBFS engine's structural copy of
Simple DB patterns now references upstream files that aren't in the tree.

**Why mitigation didn't catch it.** Arch R10 mitigation (via memory note) is
"accept gitlinks-as-tree; commit per-phase immediately." This is a *process*
mitigation, not a structural one. If any Phase 5 commit lands during a
parallel /dev session, the flip recurs. No automated check.

**Earliest detectable signal.** A pre-push hook (or CI step) that runs
`git ls-tree HEAD examples/simple_db` and asserts the result starts with
`160000` (gitlink) or fails. Currently no such check.

**Counter-mitigation (fits AC-10 doc note).** Add a new section to
`dbfs_architecture.md` (Staged Rollout / Phase 8 ship-time checks) listing the
required pre-ship grep/`git ls-tree` checks: every expected submodule path
retains `160000` (gitlink) mode in `HEAD`. Document, not script — the doc
note becomes the ship-gate item the maintainer walks through. No new AC.

---

## R9 — Submodule race with parallel /dev (per memory)

**Failure scenario.** Ship-day + 1 week (post-merge). A second SStack feature
spins up in parallel. Mid-stage, its agent runs `jj commit` while the DBFS
maintainer is mid-edit on `dbfs_engine/wal.spl`. Auto-snapshot fires between
DBFS's `git add` and `git commit`; the submodule gitlink in the staged tree
flips to 040000. The DBFS commit lands without the gitlink. Next CI: NVFS
tests fail because they reach into the submodule for fixtures.

**Why mitigation didn't catch it.** Arch R13 mitigation: "pause all parallel
sstack tracks before DBFS phase work." Same problem as R8 — process, not
structural. Worse: depends on humans coordinating.

**Earliest detectable signal.** Same as R8 — a `git ls-tree` assertion in CI
or a pre-commit hook.

**Counter-mitigation (fits AC-10 doc note).** Same Phase 8 ship-time
checklist item from R8 covers this — the doc note explicitly lists "verify no
parallel /dev tracks active during ship commit; confirm submodule gitlinks
retain `160000` mode" as one ship-gate step in `dbfs_architecture.md`. No new
AC.

---

## R10 — Extern bootstrap rebuild missed (per memory)

**Failure scenario.** Ship-day. The Phase 5 agent added one new `rt_*` extern
(say, `rt_dbfs_arena_flush`). Local `bin/simple test` passed because the
interpreter resolved it via FFI lookup. Ship merges. CI builds the release
binary using the cached SMF, which doesn't know about the new extern. Release
binary segfaults on first DBFS mount. Per memory `feedback_extern_bootstrap_rebuild`,
the wrapper falls through whitelist and silently no-ops `bin/simple build`.

**Why mitigation didn't catch it.** Arch R11 mitigation: "Any new rt_* extern
requires full bootstrap; documented in implementation handoff." Documentation
again. No spec asserts it.

**Earliest detectable signal.** A grep in CI: `grep -r 'extern fn rt_' src/`
diff vs. main; if any new `rt_*` extern, fail the job unless
`scripts/bootstrap/bootstrap-from-scratch.sh --deploy` was run in this branch
(detectable via build artifact timestamp).

**Counter-mitigation (fits AC-10 doc note).** Add to `dbfs_architecture.md`
Phase 8 ship-time checklist: "If any new `rt_*` extern was added to
`src/lib/nogc_sync_mut/db/**` since the last bootstrap, run
`scripts/bootstrap/bootstrap-from-scratch.sh --deploy` before ship and record
the resulting `bin/simple` checksum in the ship commit message." Doc note,
not script. No new AC.

---

## R11 — Compile-mode false-greens (NOT in arch D12)

**Failure scenario.** Ship-day + 12 days. A downstream user runs the DBFS
benchmarks in `--mode=native` (per their CI defaults) and reports IOPS
numbers ~10× higher than published. Investigation: per memory
`feedback_compile_mode_false_greens`, `--mode=native` stub-generation no-ops
unresolved `std.spec` calls; `--mode=smf` swallows runtime errors. Both
report PASSED. The user's "passing" benchmark was running zero work.

**Why mitigation didn't catch it.** Arch D11 says "All specs are
interpreter-mode only." This is a constraint, not a *risk in D12*. There's no
ship-gate check that the user's CI uses interpreter mode. The README/AC-10
doc doesn't ban native/smf for DBFS specs.

**Earliest detectable signal.** A test-runner assertion: every DBFS spec
prints a line like `[mode=interpreter]` and the test runner refuses to record
PASS without seeing that line. Or simpler: top-of-spec
`if mode != "interpreter": skip("DBFS specs are interpreter-mode only")`.

**Counter-mitigation (fits AC-9).** Add to every DBFS `*_spec.spl` a
single-line guard: `assert_interpreter_mode_or_skip()`. Add to Phase 8
ship-gate script: confirm at least one CI lane runs `bin/simple test` without
`--mode=` flags. Document the constraint in `dbfs_architecture.md` D11 and in
the spec file headers. **This risk needs to be ADDED to D12 as R14.**

---

## R12 — jj clobbers uncommitted Edit-tool edits (NOT in arch D12)

**Failure scenario.** Ship-day - 4 hours. The Phase 5 agent has Edit-tool
modifications staged in 3 .spl files but not yet jj-snapshotted. A second
parallel /dev fires `jj commit` for an unrelated track. jj reconciles the
working copy and removes the un-snapshotted Edit-tool changes (per memory
`feedback_jj_uncommitted_clobbered_by_parallel`). The Phase 5 agent re-runs
tests, sees them pass *because the broken change is gone*, ships. Production
builds fail because the missing changes were the fix for an exit-code bug
introduced earlier in the session.

**Why mitigation didn't catch it.** Not in D12 at all. Arch R10/R13 cover
gitlinks/submodules; this is plain working-copy edits being silently dropped.
The memory feedback exists but the architecture didn't pick it up.

**Earliest detectable signal.** An auto-`jj describe @ -m "wip"` run after
each Edit tool call. Or a `jj diff` count check before/after each parallel
agent boundary. Currently neither.

**Counter-mitigation (fits AC-10 doc note).** Add to `dbfs_architecture.md`
(Module Map Summary or new Phase 5 Process Invariants section): "After each
`*_spec.spl` or engine-source edit, immediately
`jj commit -m \"wip(dbfs): <file>\"` before issuing further tool calls. This
is a process invariant for parallel-safe DBFS work." Doc note, not agent
instruction. **This risk needs to be ADDED to D12 as R15.**

---

## R13 — BlobBackend conformance suite missing a backend variant

**Failure scenario.** Ship-day + 9 weeks. A new contributor builds a
`MemBackedArena` for unit tests in another subsystem (browser cache). Out of
ambition, they wire it as a third `BlobBackend` for DBFS so they can run
benchmarks without a block device. Their `arena_clone_range` impl violates
the unstated invariant that source and dest ranges must not overlap. DBFS's
COW path on rename-into-same-arena now silently produces wrong data — but
only on this third backend, never tested on the original two. A user using
the contributor's tooling produces a corrupt FILE_VERSION row.

**Why mitigation didn't catch it.** Arch D6 says "Arena trait IS the
BlobBackend" and lists 7 verbs — but no shared *conformance suite* runs
against every implementation. `arena_as_blob_backend_spec.spl` exists but only
exercises the NVFS Arena impl. `raw_nvme_backend_spec.spl` exercises
RawNvmeArena. There's no "every Arena impl must pass *this* test set."

**Earliest detectable signal.** A trait conformance test file that takes
`fn make_backend() -> impl Arena` as a parameter and runs the 7-verb invariant
suite. The test file would be referenced by every backend's spec.

**Counter-mitigation (fits AC-4).** Add `test/dbfs/arena_conformance_suite.spl`
(NOT a `_spec.spl` — a helper module), called from
`arena_as_blob_backend_spec.spl` AND `raw_nvme_backend_spec.spl` (rename
existing files if needed). The suite documents and tests every behavioral
invariant of the 7 verbs (overlap rules for `arena_clone_range`, idempotency
of `arena_discard`, durability semantics of `arena_append`, sealed-arena
read-only invariant). New backends must add a one-line dispatch into the
suite. **This risk needs to be ADDED to D12 as R16.**

---

## Pre-mortem Top 3 — fix-before-ship

These three would block Phase 8 if surfaced in Phase 7. They share one
property: **the architecture's mitigation is documentation or process, not a
runtime/test invariant.** That's the canonical pre-mortem failure mode.

> **Note — two different rankings.** The "fix-before-ship" Top 3 below
> answers *which risks are most under-mitigated and would block ship if
> exposed*. A separate "most-likely-to-fire-in-90-days" ranking would lead
> with **R10 (extern bootstrap rebuild)**, **R12 (jj clobbers uncommitted
> edits, fires *during* the parallel Phase 5–7 work itself)**, and
> **R5 (random-overwrite churn → user latency complaints)**. Pre-mortem
> intent is ship-blocking unmitigated risk, so we keep R11/R13/R1 as Top 3.

### #1 — R11 Compile-mode false-greens (UNREGISTERED)

**Why fix-before-ship.** This is the most likely 90-day incident. The
combination of (a) downstream CI defaulting to `--mode=native`, (b) DBFS
specs being interpreter-only, and (c) both modes reporting PASSED is a
*silent* failure mode. The user can't even tell their tests are no-ops. AC-9
explicitly says "verify in interpreter per `feedback_compile_mode_false_greens`"
but there's no enforcement in the spec files themselves. Counter-mitigation
costs one line at the top of each spec: `assert_interpreter_mode_or_skip()`.
If we don't fix it before ship, every user that runs benchmarks gets
fictional numbers.

### #2 — R13 BlobBackend conformance suite (UNREGISTERED)

**Why fix-before-ship.** AC-4 claims "pluggable backend" — but a backend
trait without a conformance suite is a leaky abstraction. The day someone
adds a third backend (and the codebase culture *encourages* this — see the
"Arena IS the BlobBackend" decision), the second-order failure surface opens.
This is the most likely 9-week incident because it scales with adoption: more
backends → more chances for invariant drift. Counter-mitigation is a single
helper file (~150 LoC) that is dispatched-into from the existing two backend
specs. Cheap. Fits AC-4 directly.

### #3 — R1 Intent-log disk persistence (HIGH, registered)

**Why fix-before-ship.** Already flagged HIGH in arch D12. Current spec
(`dbfs_engine_wal_spec.spl`) verifies LSN/CRC but not byte-level
post-flush durability. The interpreter-mode test happens to pass because
the in-memory ring is the same as the disk view *in the harness*. The bug
fires when interpreter mode is replaced with real I/O, and that happens at
some user's first power-loss event. The Instagram-reel scenario is the
canonical user case from the design doc. Counter-mitigation is a flush-count
invariant in the harness, plus a byte-level read-back assertion in
`wal_spec.spl`. ~30 LoC; tightly scoped; doesn't widen ACs.

**Honorable mentions (just below the cut):**
- R12 (jj clobbers uncommitted edits) — process risk, hard to encode as a
  spec, but lethal during the parallel Phase 5/6/7 work. Mitigate via agent
  instructions, not a spec.
- R7 (torn COMMIT records) — bug class is real and catastrophic, but the
  exact scenario (CRC accidental match) is improbable enough that R1/R11/R13
  outrank it on probability.

---

## Cross-reference index

| Risk | Spec file(s) that should catch it | Counter-mit lands in |
|---|---|---|
| R1  | `dbfs_engine_wal_spec.spl`, `power_cut_harness.spl`               | `dbfs_engine_wal_spec.spl`           |
| R2  | `dbfs_engine_checkpoint_ring_spec.spl`, `dbfs_recovery_spec.spl`  | `power_cut_harness.spl`              |
| R3  | `bench_harness_smoke_spec.spl`                                    | `bench_harness_smoke_spec.spl`       |
| R4  | `dbfs_hw_passthrough_spec.spl`                                    | `dbfs_hw_passthrough_spec.spl`       |
| R5  | `bench_harness_smoke_spec.spl` (random_overwrite)                 | `bench_harness_smoke_spec.spl`       |
| R6  | `dbfs_capability_spec.spl`, `dbfs_posix_shim_spec.spl`            | `dbfs_capability_spec.spl`           |
| R7  | `dbfs_recovery_spec.spl`, `power_cut_harness.spl`                 | `dbfs_recovery_spec.spl`             |
| R8  | (build/ship hygiene)                                               | `dbfs_architecture.md` Phase 8 ship-time doc note |
| R9  | (build/ship hygiene)                                               | `dbfs_architecture.md` Phase 8 ship-time doc note |
| R10 | (build/ship hygiene)                                               | `dbfs_architecture.md` Phase 8 ship-time doc note |
| R11 | All `*_spec.spl` (mode guard)                                     | All DBFS `*_spec.spl` headers        |
| R12 | (process invariant)                                                | `dbfs_architecture.md` Phase 5 process-invariant doc note |
| R13 | `arena_as_blob_backend_spec.spl`, `raw_nvme_backend_spec.spl`     | New `test/dbfs/arena_conformance_suite.spl` (helper) |

## Counter-mitigation count

- 13 counter-mitigations proposed (one per risk).
- 7 land inside existing specs (extensions, no new files): R1, R2, R3, R4,
  R5, R6, R7.
- 1 new helper file proposed (`arena_conformance_suite.spl`, R13).
- 4 are doc-note additions to `dbfs_architecture.md`: R8 (Phase 8 ship-time
  checks), R9 (same Phase 8 doc note), R10 (Phase 8 ship-time checks), R12
  (Phase 5 process invariants).
- 1 is a per-spec header guard (R11 — `assert_interpreter_mode_or_skip()` at
  the top of every DBFS `*_spec.spl`).
- All counter-mitigations stay within the existing 10 ACs (no scope creep)
  and within the prompt's allowed taxonomy (additional spec / additional
  bench check / additional invariant assert / additional doc note).

## Recommended D12 register additions

The architecture doc's D12 should be extended in Phase 6 (refactor) or as a
follow-up doc commit:

- **R14 (NEW)** — Compile-mode false-greens. Mitigation: `assert_interpreter_mode_or_skip()` in every DBFS spec.
- **R15 (NEW)** — jj clobbers uncommitted Edit-tool edits. Mitigation: per-edit auto-`jj commit` in Phase 5 agent instructions.
- **R16 (NEW)** — BlobBackend conformance suite missing a backend variant. Mitigation: `test/dbfs/arena_conformance_suite.spl` helper invoked by every backend spec.

*End of pre-mortem.*
