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
Gate: ~~stale_generation_reads == 0~~ during Retry 12. **Corrected (run 12):**
`stale_generation_reads` is a string the compiler never prints — grepping it
always returns 0 and reads as a PASS. Gate instead on the real message anchor
`: produced at generation ` (see the Run 12 entry under `### L7`), and note
that this is only measurable **after** `ast_gen_check_index` is wired into the
arena accessors — it currently has zero production call sites.

### L7 — Retry 12 execution (after L1, L2)
Own: run artifacts only (no source). Full Stage-4 with L5 sampler attached,
`SIMPLE_BOOTSTRAP_STAGE4=1`.

**Admission (amended 2026-07-30, supersedes the single-run wording below —
see run 10 for why):** split into two independent passes; both must pass.
No sampling of the AST-generation gate (that was rejected option (a); see
run 10).

| Pass | Env gates | Corpus | Threshold | Wall-clock budget |
|---|---|---|---|---|
| A — diagnostic (gates ON) | `SIMPLE_BOOTSTRAP_STAGE4=1 SIMPLE_AST_GEN_CHECK=1` | first 300 modules in build order (bounded; run 10's 225-module sample already covers the shared foundation + all six landed lanes' touched files with zero findings, so a prefix is representative — see run 10) | ~~`stale_generation_reads == 0`~~ **[corrected run 12: never-printed string, always false-greens — gate on `: produced at generation ` instead, and only once `ast_gen_check_index` is actually called in production]** AND OOB diagnostics `== 0` over the entire bounded corpus (zero tolerance, no sampling within the pass) | 4h (run 10 measured ~48s/module; 300 modules ≈ 4h at that rate — kill and file a bug if exceeded, do not silently truncate or extrapolate) |
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
  - **Run 11 (2026-08-01) — preflight measured, Pass A LAUNCHED.** The four
    standing blockers were re-measured rather than assumed; none survived:
    1. **LLVM seed capability: NOT a blocker (run 1's failure mode is gone).**
       `src/compiler_rust/target/bootstrap/simple` is 32MB, which *looks* like
       the no-LLVM build (the 154MB/57MB size heuristic in memory says so) —
       **the size heuristic is wrong here.** Measured positively instead:
       `native-build t.spl --backend=llvm` exits 0, emits a 25,208-byte
       `ELF 64-bit LSB pie executable`, and running it prints `2`.
       LLVM 18 (`/usr/lib/llvm-18`) is picked up by the bootstrap script.
       Do not re-derive LLVM capability from binary size; assert an artifact.
    2. **Parse/self-host: not reproduced.** The run-4..run-9 blocker was
       already dissolved by run 10 (stale `.simple/native_cache`). At HEAD the
       cache is empty (0 bytes) and `prepare_native_cache` self-clears on a
       build-context hash change, so the stale-artifact hazard is not armed.
    3. **The gates are REAL, but the plan's metric name is not.**
       `SIMPLE_AST_GEN_CHECK` is genuinely implemented in
       `src/compiler/10.frontend/core/_Ast/module_state.spl` and
       `src/compiler/10.frontend/core/_AstExpr/nodes.spl` (plus
       `src/lib/common/mem_infra/config.spl`), so Pass A is not vacuous.
       **However the literal string `stale_generation_reads` — the Pass A gate
       metric as written in the admission table above — appears NOWHERE in
       `src/**` or `scripts/**`.** Grepping for it will therefore always return
       zero and read as a PASS. That is a false-green trap: Pass A must be
       scored on the diagnostics the compiler actually emits (the
       stale-generation line from `ast_gen_check_index`, and
       `[stmt_get_tag] OOB` / `[flat-bridge] missing (stmt|expr) tag`, which is
       the pair `bootstrap-from-scratch.sh:1626` itself greps for), not on the
       plan's invented metric name. **Zero output is only a pass if the run
       also reached stage 4** — see the scoring rule below.
    4. **Resource-monitor cap: still live, but does NOT apply the way run 10
       was killed.** `kill_simple_monitor.shs` (PID 2063) is running.
       `is_simple_run_or_test()` matches only an adjacent `simple run` /
       `simple test` argv pair, so a stage `simple native-build` process falls
       to the **generic** branch: **no CPU/60s guard at all**, and only
       `KILL_ANY_MEM_MB` = **64000 MB** RSS. The 24000 MB `KILL_SIMPLE_MEM_MB`
       guard does not apply. Both thresholds are read from the *monitor's own*
       env at daemon start, so they cannot be raised live without restarting
       the daemon (which would disturb parallel lanes).
       **The real ceiling today is the host, not the cap:** at launch
       `free -g` showed 125 GB total / 1 GB free / **54 GB available** with
       **swap 7/7 GB fully consumed**. 54 GB available sits *below* the 64 GB
       kill threshold, so a genuine balloon will OOM or thrash the host before
       the monitor ever fires. If Pass A dies without a `[kill_monitor]` line
       in its log, suspect host memory pressure, not the cap.
    - **Launched:** `SIMPLE_BOOTSTRAP_STAGE4=1 SIMPLE_AST_GEN_CHECK=1
      SIMPLE_TIMEOUT_SECONDS=0 sh scripts/bootstrap/bootstrap-from-scratch.sh
      --backend=llvm --output=<scratch>/passA/out --no-mcp`, detached via
      `setsid nohup`. Deliberately **no `--deploy`** (must not clobber
      `bin/simple`) and **no `--full-bootstrap`** (must not rebuild the Rust
      seed and break other lanes). Log: `<scratch>/l7/passA/passA.log`, stage
      logs under `<scratch>/l7/passA/out/logs/x86_64-unknown-linux-gnu/`.
    - **How to score it (Pass A):** a PASS requires **all** of —
      (i) the run actually reached and completed **stage 4** (`stage4-native-build`
      log present, and the stage4 smoke `-c 'print(1+1)'` → `2`); (ii) **zero**
      `[stmt_get_tag] OOB` / `[flat-bridge] missing (stmt|expr) tag` lines;
      (iii) **zero** stale-generation diagnostics; (iv) coverage of **≥300
      modules** in build order. **False green to reject:** a grep returning
      zero because the run died in stage 2/3 and never exercised the gate, or
      because it was scored on `stale_generation_reads` (a string the compiler
      never prints). Always confirm the module count and the stage-4 artifact
      before reading zero diagnostics as a pass.
    - Pass B (gates OFF, full ~1494 modules, `check-stage4-memory-gate.shs`)
      is **not** started; it is only meaningful after Pass A is scored.
  - **Run 11 (2026-08-01) — DIED BEFORE STAGE 1. VOID, not a pass.** The run
    aborted with `error: Rust runtime authority changed during private
    admission` and produced **zero** stage logs. Cause: a parallel lane ran
    `cargo build --profile bootstrap` against the shared
    `src/compiler_rust/target/bootstrap/` while the script was freezing its
    private copy of the seed. `bootstrap-from-scratch.sh` snapshots that
    directory before and after the copy (lines ~1108-1127) and aborts by design
    when the two snapshots differ. **The run exercised nothing** — it must not
    be scored, in either direction. At failure the host had ~50 GB available of
    125 GB with **swap fully exhausted (7/7 GB)** and a `simple` process at
    7.8 GB RSS.
  - **Run 12 (2026-08-01) — NOT LAUNCHED. Blocked, deliberately.** Four
    independent blockers were measured at preflight; the last is decisive on
    its own.
    1. **The isolation knob assumed by the retry plan does not exist.** The
       intended fix for run 11 was "copy the seed to a private directory and
       point the run at it". There is no such knob.
       `runtime_origin_absolute` is hardcoded relative to the *current working
       directory* — `runtime_origin_absolute="$(absolute_path
       src/compiler_rust/target/bootstrap)"` (`bootstrap-from-scratch.sh:1063`)
       — and `SIMPLE_RUNTIME_PATH` is **exported by the script itself**,
       overwriting any caller value: `export
       SIMPLE_RUNTIME_PATH="$(pwd)/src/compiler_rust/target/bootstrap"`
       (line 989). The script's only flags are `--deploy --release
       --full-bootstrap --pure-simple --full-cli --mode --verbose --no-mcp`
       (plus `--backend`/`--output`); there is **no `--runtime-path`** and no
       `${SIMPLE_RUNTIME_PATH:-}` override. Isolating the seed therefore
       requires running from a full private *repo copy*, not an env var.
    2. **A private seed copy taken now would be torn.** Two
       `cargo build --profile bootstrap` processes were actively rewriting the
       shared 6.9 GB seed tree at preflight (PIDs 935743 and 1020591, the
       latter started 3 s into the check), plus a `cargo test -p
       simple-compiler --features llvm`. Copying a 6.9 GB tree mid-write
       reproduces run 11's exact race, except the corruption would be silent
       rather than caught by the authority check. The seed must be quiescent
       before any copy.
    3. **Memory has no reserve and the OOM killer targets this workload.**
       Sampled over 20 s: `MemAvailable` 51.3 → 47.9 GB and falling, **swap
       free 0 MB throughout**. A *second* Stage-4 lane was already running
       (PID 262451, `stage4-spdev-current/global-cycle3-stage2`, `simple
       native-build --backend cranelift`) and growing — 8.4 → 9.4 GB RSS over
       ~2 min. Critically, the host runs `earlyoom -r 3600 --prefer
       ^(simple|rustc|cc1|cc1plus|lto1|collect2|qemu-system|ld)` — it
       **preferentially kills `simple` and `rustc`**. With swap already at 0 %
       free, earlyoom's swap precondition is permanently satisfied, so only
       memory need cross its threshold to fire. This confirms and sharpens the
       known finding that the 64 GB resource monitor cannot protect the run:
       `is_simple_run_or_test()` matches only an adjacent `simple run`/`simple
       test` argv pair, so a stage `simple native-build` falls to the generic
       branch — an OOM fires before the monitor does, and now with an OOM
       killer explicitly biased toward `simple`. Launching a second 4 h Stage-4
       lane would likely kill both it and the 15-min-old lane already running.
    4. **Gate criterion 3 is structurally unmeasurable — a SECOND false
       green.** Beyond the already-recorded trap that the literal
       `stale_generation_reads` is a string the compiler never prints, the
       underlying check is **never invoked in production**.
       `ast_gen_check_index` (`src/compiler/10.frontend/core/_AstExpr/nodes.spl:326`)
       has **zero production call sites** — it is not called from
       `expr_get_tag`, `stmt_get_tag`, or any arena accessor; its only callers
       are unit tests (`test/01_unit/compiler/ast_arena_generation_spec.spl`,
       `ast_arena_harden_spec.spl`). So a real Stage-4 native build emits **no
       stale-generation line regardless of actual staleness**, and criterion 3
       reads zero by construction. Spending ~4 h to produce an unscoreable
       result is the same void outcome as run 11, just discovered before the
       compute is burned rather than after.
  - **Corrected diagnostic strings (use these, not `stale_generation_reads`).**
    The stale-generation message is assembled at runtime, which is why no fixed
    literal exists —
    `ast_gen_stale_message()` (`_AstExpr/nodes.spl:323-324`) builds
    `stale <kind> <idx>: produced at generation <N>, arena now at <M>`, printed
    at `nodes.spl:338` at most once per generation. The only non-interpolated,
    greppable anchor is **`: produced at generation `** (secondary: `, arena
    now at `). It is gated on `SIMPLE_AST_GEN_CHECK=1` or
    `SIMPLE_BOOTSTRAP_STAGE4=1` (`nodes.spl:316-321`). The OOB markers are
    real and *are* emitted in production: `[stmt_get_tag] OOB`
    (`core/ast_stmt.spl:499`), `[expr_get_tag] OOB`
    (`_AstExpr/accessors.spl:108`), `[flat-bridge] missing expr|stmt tag`
    (`_FlatAstBridge/convert_nodes.spl:674` and `:1359`); the existing gate
    regex `'\[stmt_get_tag\] OOB|\[flat-bridge\] missing (stmt|expr) tag'`
    lives at `bootstrap-from-scratch.sh:1626` and
    `check-stage4-selfhost-parse-memory-multifile.shs:253`.
  - **Prerequisites before any run 12 relaunch** (all four, in order):
    (a) wire `ast_gen_check_index` into the arena accessors so criterion 3 can
    actually fire, and re-specify the gate against `: produced at generation `
    — otherwise Pass A cannot be scored; (b) wait for the shared seed tree to
    go quiescent (no `cargo build --profile bootstrap` running) before copying
    it; (c) isolate by running from a private repo copy, since no runtime-path
    knob exists — then verify the run's `runtime:` line points at that copy;
    (d) require swap headroom > 0 and no competing Stage-4 lane, or serialise
    against it. Arm the watcher on failure signatures (`error:`, `Killed`,
    `OOM`, `parser_error`, `OOB`), not only on success markers.
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
