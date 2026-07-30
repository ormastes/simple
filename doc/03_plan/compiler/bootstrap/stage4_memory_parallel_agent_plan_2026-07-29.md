# Stage-4 Memory/Ownership Parallel-Agent Plan (2026-07-29)

Research: `doc/01_research/compiler/bootstrap/stage4_memory_ownership_research_2026-07-29.md`
SPipe mission: `.spipe/stage4_memory_harden/state.md`

## Shared parts — FIXED BEFORE LANE START (this session, so lanes don't conflict)

The following shared foundations are already landed; **no lane may edit these
files' touched regions without coordinating through this plan**:

| Shared piece | File(s) | Status |
|---|---|---|
| `CowEnv` dirty tracking, `project_preserving_bindings`, `refreshed_global_entries`, `global_bindings_iter` | `compiler/src/value.rs` | LANDED |
| Frame-lifecycle protocol factored (`sync_captured_globals_with`, lambda variants, `refresh_bound_globals_from_store`, publish pub(crate)) | `compiler/src/interpreter_call/core/function_exec.rs` | LANDED |
| `exec_lambda` protocol wiring | `compiler/src/interpreter_call/core/lambda.rs` | LANDED |
| `copy_back_block_writes` (3-channel write-back) | `compiler/src/interpreter/block_exec.rs`, `compiler/src/interpreter/expr/control.rs` | LANDED |
| Root import-binding markers | `compiler/src/pipeline/module_loader.rs` | LANDED |
| Heap byte counters + externs (`rt_heap_live_bytes` etc.) | `runtime/src/value/heap.rs` | LANDED |
| Lambda regression suite | `compiler/tests/interpreter_flattened_module_globals.rs` | LANDED |

Rule for all lanes: append-only in the shared test file; new tests go in NEW
`compiler/tests/*.rs` files named per lane to avoid merge conflicts.

## Lanes (disjoint file ownership)

### L1 — vmm ExecutionLimit red (blocker, run FIRST)
Own: new `compiler/tests/` debug harness only; fix location TBD by root cause.
`real_vmm_sparse_init_preserves_active_root` hits 10M-op limit in isolation.
Determine: infinite loop from a stale global read vs. genuinely heavy test.
Use `SIMPLE_DEBUG_LAMBDA_SYNC=1` + op-count bisect. If a loop: fix in the
frame protocol (coordinate — function_exec.rs is shared). Deliverable: green
test or filed bug with exact loop site.

### L2 — test-harness thread-local isolation
Own: `compiler/tests/interpreter_flattened_module_globals.rs` helper fns +
`interpreter::clear_interpreter_state` internals (`interpreter_state.rs`).
The reentrant test passes alone, fails in-suite: MODULE_GLOBALS* thread-locals
leak across tests on reused threads. Fix `clear_interpreter_state` to reset
ALL owner maps (BINDINGS_BY_OWNER, INITIAL_BY_OWNER, ENV_BY_OWNER,
FUNCTION_MODULE_OWNER, CURRENT_EXEC_MODULE) or serialize via a shared mutex.

### L3 — aux-byte accounting (containers)
Own: `runtime/src/value/collections.rs`, `dict.rs`, string/object modules.
Extend the landed header-byte counters with backing-buffer bytes: report
capacity vs length bytes per kind; add `clear_reuse()` vs `release_storage()`
distinction on arrays. Do NOT touch heap.rs counter internals — add new
`note_aux_{alloc,free}` hooks in heap.rs bottom (append-only region).

### L4 — hosted interpreter memory truth
Own: `compiler/src/interpreter_extern/memory.rs`, `src/runtime/runtime_memory.c`.
Real `memory_usage()` (read /proc/self/statm or counters), allocation metadata
for hosted `rt_alloc` so `rt_free` actually frees; capability/version externs
`rt_mem_profile_abi_version()` / `rt_mem_profile_features()`.

### L5 — OS-truth sampler + phase snapshots
Own: NEW `src/app/memstat/` (.spl) + `scripts/check/check-stage4-memory-gate.shs`.
Out-of-process sampler: `/proc/<pid>/smaps_rollup` + cgroup v2 files → CSV
(commit, binary sha256, engine, corpus hash per row). Phase-end snapshot line
in driver (`src/compiler/80.driver/driver_log_helpers.spl`) using the new
`rt_heap_*` externs — fixed-format single line, no per-event Simple strings.
SSpec spec for the gate (spipe skill): byte-slope assertions over corpus tiers.

### L6 — typed AST arena IDs (design + incremental)
Own: `src/compiler/**` AST arena modules (pure-Simple side).
Generation-bearing IDs behind SIMPLE_BOOTSTRAP_STAGE4 debug accessors first
(stale-read DIAGNOSIS, not representation change): reset bumps a generation
counter; debug accessor logs generation mismatch instead of OOB cascade.
Gate: stale_generation_reads == 0 during Retry 12.

### L7 — Retry 12 execution (after L1, L2)
Own: run artifacts only (no source). Full Stage-4 with L5 sampler attached,
`SIMPLE_BOOTSTRAP_STAGE4=1`.

**Admission (amended 2026-07-30, supersedes the single-run wording below —
see run 10 for why):** split into two independent passes; both must pass.
No sampling of the AST-generation gate (that was rejected option (a); see
run 10).

| Pass | Env gates | Corpus | Threshold | Wall-clock budget |
|---|---|---|---|---|
| A — diagnostic (gates ON) | `SIMPLE_BOOTSTRAP_STAGE4=1 SIMPLE_AST_GEN_CHECK=1` | first 300 modules in build order (bounded; run 10's 225-module sample already covers the shared foundation + all six landed lanes' touched files with zero findings, so a prefix is representative — see run 10) | `stale_generation_reads == 0` AND OOB diagnostics `== 0` over the entire bounded corpus (zero tolerance, no sampling within the pass) | 4h (run 10 measured ~48s/module; 300 modules ≈ 4h at that rate — kill and file a bug if exceeded, do not silently truncate or extrapolate) |
| B — byte-residue (gates OFF) | `SIMPLE_BOOTSTRAP_STAGE4=1` only (`SIMPLE_AST_GEN_CHECK` unset) | full corpus, all ~1494 modules | L5 gate thresholds unchanged (`check-stage4-memory-gate.shs`: RSS ceiling AND byte-slope, not RSS alone) | 30 min (run 10 measured ~7min gates-off; 30 min gives ~4x headroom) |

If Pass A ever reports a nonzero diagnostic, double the corpus bound and
rerun Pass A before admission — do not waive it. Pass B alone or Pass A alone
does not satisfy admission; both are required.

## Lane status (final, 2026-07-29)

- L1 LANDED 89a3fd511edf (MMIO-journal × per-page quadratic, 34.6M→19k ops)
- L2 LANDED 941e0b646dd (RECURSION_DEPTH underflow + shared op budget; both
  suite reds; 36/0)
- L3+L4 LANDED 3e4cd8fc7e3 (aux buffer bytes; hosted memory truth)
- L5 LANDED 76e43b18741 (memstat sampler + RSS gate, 2/2)
- L6 LANDED 5eef43f775e (arena generation diagnostics, 5/5); hardened later
  by SIMPLE_AST_GEN_HARDEN (a9e61476da97, 4/4)
- L7 IN PROGRESS — run history:
  - Run 1 (llvm): stage2 fails — seed built without LLVM feature; switched
    to cranelift (environmental, not a lane defect).
  - Run 2 (cranelift): stage2 PASS; stage3 SIGABRT = env::set_var NUL panic
    in the bootstrap env mirror. Root-caused + fixed 455ed8321730
    (env_value_nul_free guards; mirror is a cache over authoritative arrays).
  - Run 3 (cranelift, post-NUL-fix): stage2 PASS; NUL abort GONE; stage3 now
    exit 132 SIGILL, stage3-native-build.log tail: "runtime error: field
    access on nil receiver". CAVEAT: this run compiled the LIVE working copy
    while parallel agents were mid-edit in src/compiler — attribution
    unreliable. Rerun required from a consistent tree (all lane edits now
    landed at a9e61476da97).
  - Runs 4-8 (cranelift, hermetic worktree): stage2 sanity PASS; stage3
    fails with a parse error in `vhdl_codegen_helpers.spl`. Run 4 recorded
    this as a `Result<(), E>` grammar divergence — **that diagnosis is
    RETRACTED** (see
    doc/08_tracking/bug/stage2_parser_result_unit_generic_divergence_2026-07-29.md).
    Runs 5-8 established the hermeticity requirements: consistent tree (no
    mid-edit agents), origin-only content, a real `.git` (provenance binds
    HEAD/dirty), no symlinks under `src/compiler_rust` (fingerprint check),
    an isolated build dir, and clean `git status`.
  - Run 9 (2026-07-30, origin 110f743b2a2, faithful stage-3 invocation):
    **the parse failure is a parser STATE bug, not a grammar gap, and it is
    the remaining L7 blocker.** Measured with a real stage-2 binary: the
    unit-generic construct, the inline-if-as-match-subject construct, the
    exact failing block, and the ENTIRE victim file all parse clean in
    isolation at both origin and the run-8 pin (byte-identical files); the
    file fails ONLY in the whole-tree focused build, first erroring at the
    statement after a `match` block's last arm. `SIMPLE_AST_GEN_CHECK=1`
    reported **zero** stale-generation/OOB diagnostics during the failing
    run — so the L6 gate is clean and the memory/arena half of the
    admission criteria is met; what remains is this parse-state defect.
    Full evidence, three ranked hypotheses, and the repro:
    doc/08_tracking/bug/stage3_whole_tree_parse_state_vhdl_helpers_2026-07-30.md
  - Also found in run 9: a non-closure whole-tree build cannot even start —
    `src/app/__init__.spl` and `src/compiler/__init__.spl` both sanitize to
    module `__init__`, aborting the multi-root scan. `--entry-closure`
    masks it. Filed in the same bug doc.
  - Run 10 (2026-07-30, pinned 110f743b2a2, cleared `.simple/native_cache`,
    gates ON: `SIMPLE_AST_GEN_CHECK=1 SIMPLE_MEM_SNAPSHOT=1
    SIMPLE_GEN_ARENA_CHECK=1`): **stage 3 reached and progressing with ZERO
    parse errors** — the run-9 parse failure did NOT recur. A separate bisect
    established that failure was a **STALE `.simple/native_cache` artifact**,
    not a compiler defect: 3/3 clean-cache runs of the exact repro on the exact
    commit compiled all 1494 modules with 0 `parser_error`. That dissolves the
    run-4..run-9 L7 blocker entirely. Run 10 was killed by our own 3h timeout,
    not by a defect — the stage-3 log was still being appended at the kill
    instant. Gates at kill: **0 parse errors, 0 stale-generation, 0 OOB** across
    ~225 stage-3 modules. Stage 4 never executed ⇒ **byte gates UNVERIFIED, L7
    NOT admissible.**
  - Scope caveat on run 10: the worktree was pinned at 110f743b2a2, which still
    carried `ZZZTRACE` debug prints that origin has since removed. The verdict
    applies to THAT commit, not to current origin nor to the memory-infra work
    landed on 2026-07-30. **A confirming run on current origin is still owed.**
  - Run 10 (cost measurement): measured the diagnostic gates'
    cost directly. `SIMPLE_AST_GEN_CHECK=1` gates-ON covered 225 modules in
    3h (self-imposed budget, killed at the limit) ≈ 48s/module; the same
    corpus gates-OFF covered 1494 modules in ~7min ≈ 0.28s/module — a ~170x
    slowdown. A full gates-ON Stage-4 run therefore projects to ~20h and
    cannot be produced by one practical run. **The admission criteria as
    originally written ("zero stale/OOB diagnostics AND byte-residue gates"
    over a full run) are self-defeating: no single run can produce that
    evidence.** Two repair options were identified: (a) sample the
    generation check instead of validating every AST access — needs a new
    compiler-side sampling implementation; (b) split admission into a
    bounded gates-ON diagnostic pass plus a full gates-OFF byte-gate pass —
    needs no compiler change. **RESOLVED 2026-07-30: option (b) chosen** —
    it needs no compiler-side work (option (a)'s sampling logic is
    unimplemented and adds scope/risk) and is executable as soon as a test
    runner exists. See the amended admission table under `### L7` above,
    which supersedes this bullet and the pre-run-10 "Admission criteria
    unchanged" wording it replaces.
  - Successor plan for the M-milestones:
    doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md.

## Sequencing

```
[shared parts: DONE] → L1, L2, L3, L4, L5, L6 in parallel → L7 (needs L1+L2; wants L5)
```

Later PRs (post-L7, from research doc): transactional regions,
GlobalCellId/ModuleState, trace descriptors — each is a separate plan entry
once Retry 12 data exists.

## Conflict rules

- One lane per file; exceptions listed above must land via smallest-diff Edit
  and immediate commit (jj), per `.claude/rules/vcs.md` anti-revert protocol.
- All interpreter behavior changes need a regression in a lane-owned test file
  run under the interpreter engine.
- Any new `rt_*` extern: note bootstrap-rebuild requirement
  (`feedback_extern_bootstrap_rebuild`).
