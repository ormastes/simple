# shard_mem_clamp ignores enclosing cgroup memory.max

Status: v2 half fixed by 2335ee01c17 (merged, ancestor of release/1.0.0); v1
half fixed by the 2026-11-05 change recorded in Evidence below. Bug DB:
`doc/08_tracking/bug/bug_db.sdn` (row: P2, filed 2026-10-19, owner
`src/app/cli/shard_mem_clamp.spl`, `src/app/bootstrap_builder/worker.spl`).

A managed Linux worker filters SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB out of the
compiler environment, and shard_mem_clamp reads host MemAvailable, so HIR
fanout inside a cgroup-contained build is sized by the host's memory instead
of the cgroup's memory.max.

## Root cause (as diagnosed)

Two halves:

1. Managed-worker environment: `src/app/bootstrap_builder/worker.spl`
   (`builder_worker_environment_v1`) and `src/app/bootstrap_builder/linux_worker.spl`
   (`builder_linux_environment_v1`) rebuild the child environment from the
   `env_vars()` snapshot. Both copy every variable through, replacing only the
   owned cache paths and TMP/TEMP/TMPDIR; neither drops
   SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB. The RSS watchdog export therefore
   reaches the compiler. (Also confirmed by 2335ee01c17's message: "no env
   filter of the budget was found in bootstrap_builder".) No code change was
   needed for this half on release/1.0.0.
2. shard_mem_clamp: the clamp sized fanout from host MemAvailable and the
   declared SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB only. cgroup v2 memory.max
   (systemd-run -p MemoryMax=, container and runner slices) is an enforced cap
   on the whole tree that no wrapper exports; inside a 24 GiB scope on a
   121 GB host the clamp admitted every requested worker and the kernel
   OOM-killed the tree. cgroup v1 hosts (memory/memory.limit_in_bytes, e.g.
   older distros, Docker on v1) had the same gap: with no "0::" row in
   /proc/self/cgroup the probe found no bound at all.

## Fix

- 2335ee01c17 (2026-10-19, already merged before this lane): v2
  memory.max chain walk, smallest numeric level in kB tightens the declared
  tree budget.
- 2026-11-05 (this lane): cgroup v1 support.
  `shard_cgroup_v1_memory_path_from_proc` finds the memory controller row in a
  v1/hybrid /proc/self/cgroup table; `shard_cgroup_v1_limit_paths` walks
  memory.limit_in_bytes from the leaf cgroup up to the v1 root;
  `shard_cgroup_v1_limit_kb_from_fields` takes the smallest numeric limit,
  ignoring the v1 "unlimited" numeric sentinel (>= 2^62 bytes,
  9223372036854771712) as well as junk/unreadable levels. The live
  `shard_cgroup_memory_max_kb` probes both the v2 unified row and the v1
  memory controller row and keeps the tighter bound, so hybrid hosts take the
  min of the two hierarchies.

## Evidence (2026-11-05, work branch work/libbug-linux-cgroupclamp-20261105)

TDD on the release/1.0.0 base, seed binary
`build/phase_snapshots/phase1_1793422538/simple`, cwd = worktree root.

- RED: `test/01_unit/app/cli/shard_mem_clamp_spec.spl` +3 examples (v1 table
  parse, v1 limit path walk, v1 sentinel/limit selection) failed with
  `semantic: function ... not found`; 29 examples, 5 failures (2 pre-existing
  macOS-gated `vm_stat` examples already fail on this Linux seed at baseline).
- GREEN: same spec 29 examples, 2 failures -- only the pre-existing macOS
  pair remains; all 3 new v1 examples pass.
- Re-run, touched/adjacent modules, all PASS (interpreter):
  `native_build_shard_admission_spec` 11/11, `shard_commit_admission_spec`
  12/12, `shard_default_threads_spec` 4/4, `build_memory_reserve_spec` 10/10,
  `native_build_shard_child_no_parse_fanout_spec` 4/4,
  `bootstrap_capsule_shard_wiring_spec` 7/7,
  `bootstrap_parse_shard_dispatch_spec` 1/1, `parse_shard_orphan_reclaim_spec`
  5/5, `bootstrap_builder/worker_spec` 2/2, `linux_worker_spec` 6/6,
  `managed_suite_environment_spec` 2/2.
- Env-filter half: verified by source inspection of both managed-worker env
  builders (full snapshot pass-through; no SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB
  filter exists on this branch), corroborated by worker/linux_worker specs
  above. Not a live cgroup v1 host on this machine (cgroup2fs,
  `0::/user.slice/...`), so the v1 live probe path is covered by the pure
  helpers only; the existing opt-in live pin
  (SIMPLE_SPEC_EXPECT_CGROUP_MEMORY_MAX_KB) still covers v2.
