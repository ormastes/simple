# native_project / core-C Backlog — Items + Parallel-Agent Execution Plan (2026-07-26)

Successor to `native_build_open_bugs_plan_2026-07-15.md`, scoped to the
`pipeline::native_project` + core-C runtime area. Every item below is **open**
as of `14f46d1045e7`. Closed in that commit and excluded here: the silent
fat-runtime fallback (now a gated hard error) and the missing failure
diagnostic (now a level-gated probe).

## Items

| # | Item | Where | Effort | Needs cargo? | Status after round 1 |
|---|---|---|---|---|---|
| I1 | core-C archive rename **ENOENT** flake | `driver/src/cli/init.rs:184` | S | yes | **ROOT-CAUSED + FIXED** |
| I2 | 25 pre-existing `pipeline::native_project` failures | `tests.rs` + selection code | M | yes | 5 root causes; 4 need a decision |
| I3 | staging dirs leak into `.simple/` unbounded | `scripts/resource/disk-retention.shs` | S | no | premise corrected; diff ready |
| I4 | fallback asymmetry: `~354` unfiltered vs `~371` filtered | `config.rs` | S | no | **CLOSED — leave as-is** |
| I5 | 238 crate-wide failures; panic `no entry found for key` | `codegen/common_backend.rs:937` | L | yes | **ROOT-CAUSED + FIXED** (238 → 108) |
| I6 | `pending()` false-green: `it` block still counts as pass | `bdd.rs`, `runtime_native.c`, `spec.spl` | M | no | 3 lanes needed, not 2 |

### I1 — core-C rename ENOENT (ROOT-CAUSED + FIXED, see Round 1 results)
Filed: `doc/08_tracking/bug/core_c_runtime_archive_rename_enoent_flaky_2026-07-26.md`.
The "no external deleter" elimination in that bug's table turned out to be wrong
reasoning — see Round 1 below for the actual cause and why the evidence misled.

### I2 — the 25 native_project failures
Present on pristine `origin/main`; confirmed unrelated to the 2026-07-26 change
by a worktree A/B (169 passed / 25 failed on both sides, identical names).
Heavily clustered in runtime-bundle selection (`test_runtime_bundle_*`,
`test_stage4_*`). Unknown whether one root cause or several.

### I3 — staging dir leak
Success path calls `TempDir::keep()`, so every successful build leaves a
`.simple/native-objects-XXXXXX/` behind — 13 accumulated over 4 days.
`scripts/resource/disk-retention.shs` sweeps `build/` only, never `.simple/`.
Fix is either an age-based sweep at build start or extending disk-retention's
container list. Note the guard test `native_object_staging_survives_cache_clean`
encodes why staging lives beside the cache — do not relocate it blindly.

### I4 — fallback asymmetry
`config.rs` `~354` pushes `find_runtime_library()` output unfiltered; the
structurally identical `~371-372` filters via
`runtime_archive_has_bootstrap_cli_symbols`. **Deliberately not changed** in
`14f46d1045e7`: with I-hard-error in place, `~354` is only reachable when no
core-C sources exist (deployed compiler), where an unfiltered prebuilt archive is
correct. Revisit only with evidence that a wrong archive reaches it.

### I5 — 238 crate-wide failures
Baseline on clean `HEAD`: `3219 passed; 238 failed`. Distribution: 79
`codegen::codegen_shared_tests`, 53 `mir::lower`, 51 `codegen::codegen_instr_tests`,
25 `pipeline::native_project` (= I2), 12 `lint::tests`, 6 `hir::lower`. Common
panic: `no entry found for key` at `codegen/instr/body.rs:613`, then
`[CODEGEN-STUB-FALLBACK]`. A single map-population bug likely explains the
largest clusters.

### I6 — `pending()` false-green
`record_test_result(.., true, true)` at `bdd.rs:782` counts a pending `it` block
as a pass; the native twin `rt_bdd_it_end` in `runtime_native.c` has the same
defect. Filed at
`doc/08_tracking/bug/spec_pending_call_still_counts_it_block_as_pass_2026-07-25.md`.

## How agents are run on these items, in parallel

The hard constraint is **contention on one repo**, learned the expensive way on
2026-07-25/26. The model:

1. **Exactly one agent owns cargo and the main working tree.** Concurrent
   `cargo` in one workspace serialises on the target-dir lock and, worse, two
   agents editing the same file silently invalidate each other's runs. That
   builder agent is told explicitly that it owns the lock.
2. **Every other agent is read-only** (grep/read; static analysis, design,
   root-cause-by-inspection) **or worktree-isolated.** Read-only lanes can run at
   any multiplicity; they never touch the tree.
3. **Worktree isolation when a lane must build:** `git worktree add --detach
   <ref>`, apply only that lane's hunks, and reuse `CARGO_TARGET_DIR` from the
   main checkout. This keeps a verification build at ~1.5 min instead of a cold
   rebuild, and it is the *only* valid way to A/B a change in a repo other
   sessions are writing to.
4. **Never verify against the working tree.** Other sessions' in-flight edits
   live there. On 2026-07-26 the tree's `common/cc_detect.rs` had a function
   deleted, so `origin/main`'s `tools.rs` would not compile in-tree, and
   committing the tree's copy would have reverted that session's work. Build the
   commit from `origin/main` blobs plus your own hunks.
5. **Controls must be proven, not assumed.** Before trusting a control run:
   assert the revert actually landed (`grep -c '<marker>' == 0`), and confirm a
   `test result:` line exists — `exit=101` with no such line is a *compile
   error*, and diffing failure names against it reports every failure as new.
   Both traps fired on 2026-07-26 and both produced confident, wrong readings.
6. **Synthesis stays with the parent.** Sub-agent conclusions are treated as
   claims, not findings, until checked: one lane's "external deleter" conclusion
   was refuted in a single command by the 13 surviving orphan dirs.
7. **Landing is serialized through the parent** via git plumbing
   (`GIT_INDEX_FILE` + `commit-tree`), with a revert guard (`git diff --numstat`
   must show exactly the intended files, zero unexpected deletions) and a
   fetch/re-derive retry loop, since `origin/main` moves under long operations.

### Lane assignment for this round

| Lane | Item | Mode |
|---|---|---|
| A | I5 codegen `no entry found for key` | **builder** — owns cargo + main tree |
| B | I2 the 25 native_project failures | read-only static analysis |
| C | I3 staging leak + I4 asymmetry re-check | read-only, proposes diffs only |
| D | I6 `pending()` false-green | read-only, both Rust + C twins |

I1 was not assigned a lane in this round's table — it was already being worked by
a builder lane carried over from the previous round, which is what found it.

## Round 1 results

### I1 — ROOT-CAUSED and FIXED
`cleanup_stale_db_files()` (`driver/src/cli/init.rs:184`, called unconditionally
from `init_runtime()`) recursively `WalkDir`s `.simple/` and deletes **every**
file whose extension is `tmp` — despite its own doc comment naming only
`*.sdn.tmp` and `*.cache.tmp`. clang stages each object as
`<name>-<hash>.o.tmp` in the output directory, and native-build stages objects
under `.simple/`. So **any `simple` invocation anywhere in the repo deleted the
live temporaries of any concurrently running compile.**

Confirmed by canary, independently of the reporting lane: create
`.simple/mycanary/core_c_runtime/{runtime_native-9dd12f74.o.tmp, runtime_native.o,
notes.txt, db.sdn.tmp}`, run `bin/simple --version` → both `*.tmp` gone, `.o` and
`.txt` survive.

Why the earlier investigation missed it, recorded so the mistake is not repeated:
- The deleter is a **different process**, so `strace -f` on the test process
  correctly showed no mid-build unlink. That evidence was sound and was
  misread as "nothing deletes it".
- "13 orphaned staging dirs survived, so there is no sweeper" was **wrong
  reasoning**: the sweep deletes `*.tmp` *files*, never directories. Surviving
  directories were never evidence about a file-level sweeper.
- It looked timing-sensitive because it depended on another process starting
  during the ~seconds-long window of a specific clang invocation. Observers did
  not suppress it; they merely changed that window.

Fix: match only `*.sdn.tmp` / `*.cache.tmp` via a new `is_stale_db_temp()`, with
regression test `stale_db_cleanup_spares_native_build_object_temporaries`.
The pure-Simple twin (`lib/std/src/db/persistence.spl:247`) was already correctly
scoped and needed no change. **The deployed `bin/simple` keeps the old behaviour
until it is rebuilt and redeployed.**

### I2 — 5 root causes, and a 20-test cascade
`test_core_lane_runtime_required_abi_stdout_stderr_and_values` panics while
holding `runtime_bundle_env_lock`, poisoning it for the 20 tests that lock it
later — so **20 of the 25 are one cascade**, not 20 defects. Underlying causes:
core-nil is `3` not `0` and the probe still expects `0` (stale test);
`test_cxx_abi_symbols_are_not_stub_candidates` is macOS-only but asserted
unconditionally; the Stage4 capsule now fail-closes on `.init_array` where the
test expects a strip; `rt_transient_array_scope_{begin,pause,end}` are in
`CORE_REQUIRED` but absent from `src/runtime/simple_core/`; one import-map owner
failure undetermined. Four of these are **behaviour-vs-test decisions for the
user**, not mechanical fixes — see the lane report before acting.

### I3 — premise was wrong, item rescoped
`.keep()` is **not** on the success path: `mod.rs:1037` is the link-failure path
and `mod.rs:1049` is opt-in via `SIMPLE_KEEP_NATIVE_OBJS` (nothing sets it). A
successful build already self-cleans on `Drop`. The real leak sources are
SIGKILL'd builds (destructors never run) and deliberately kept link-failure
dumps. Scope is also larger than stated: 14 dirs in `.simple/` plus 5 in
`build/` (~616 MB total). Fix is to extend `disk-retention.shs` — which already
sweeps this exact prefix under `build/bootstrap` — reusing its existing
`path_is_busy` + `MIN_AGE_HOURS` guards. Sweeping at build start was rejected:
parallel agent builds share `.simple/`, and it would delete kept failure dumps.

### I4 — CLOSED, leave as-is
Filtering `~354` by `runtime_archive_has_bootstrap_cli_symbols` buys nothing:
`nm -g --defined-only` on the 34 MB generic seed archive — the very "~28x larger"
runtime the warning is about — shows **all 9** required symbols defined, so it
passes the filter anyway. Filtering would instead break the legitimate deployed
case. Only a lane-identity check would discriminate; no evidence justifies one.

### I5 — ROOT-CAUSED and FIXED (238 → 108, 0 regressions)
One drifted hand-maintained mirror explains **130 of the 238**.
`common_backend.rs:937/964` prunes runtime-import declarations to the names in
`referenced_call_names(&functions)` (a size optimization keeping baremetal links
lean). That collector mirrors the codegen lowering table by hand and had drifted:
~20 `MirInst` variants handled, everything else dropped via `_ => {}`. Codegen
then indexes the map directly (`runtime_funcs["rt_generator_get_state"]` at
`codegen/instr/body.rs:613`, `ctx.runtime_funcs[..]` in `collections.rs`,
`resolve_runtime_func` in `helpers.rs:308`) — a missing name is a panic, caught
by the stub-fallback wrapper as `[CODEGEN PANIC] ... no entry found for key`.

Two structural gaps: (1) **function-level metadata is invisible to a
per-instruction walk** — generator/async state machines lower from
`MirFunction::{generator,async}_states`, not from any `MirInst`, so
`rt_generator_get_state` could never be collected; (2) missing instruction arms
(all `Vec*`/`Gpu*`, `BuiltinMethod`, `FStringFormat`, `TupleLit`,
`Pointer{New,Ref,Deref}`, probes, `Par*`, contract/unit checks, `NeighborLoad`).
Control: with the filter bypassed, both big clusters went to ~1 failure each —
one cause, both clusters.

A second, independent bug fixed alongside: `codegen/instr/units.rs:117`
`compile_unit_widen` emitted `sextend.i64` gated only on MIR `from_bits`; when
the value was already materialized as i64 the Cranelift verifier rejected it.
Now gated on `builder.func.dfg.value_type(val).bits() < 64`.

Fix is purely additive to `referenced_call_names` (+299) + the widen gate.
Verified twice: by the lane on the tree (3350 passed / 108 failed, was
3219/238) and by the parent on an origin/main worktree rebase (674/0 across
both codegen modules, real recompile). Remaining 108 are separate items:
53 `mir::lower` (51 = gpu_errors tests expecting `Err` where lowering now
succeeds), 25 = I2, 12 `lint::tests` (parser rejects `Parallel` attribute in
fixtures), 6 `hir::lower`, 12 singletons (incl. a *different*
`no entry found for key` at `mir_inline.rs:237`).

### I6 — three lanes, not two
`std.spec` (`spec.spl:186`) has the same defect, so Rust + C + `std.spec` must
move together. The real defects are `bdd.rs:796` (bumps the *passed* counter) and
`bdd.rs:767` (the enclosing `it` records a second, non-skipped `passed=true`) —
**not** the `(true, true)` arguments, which are already honoured. No pending
marker reaches C at all: no `rt_bdd_pending*` symbol exists and `stmt_lowering.rs`
has no `pending` arm, so `rt_bdd_it_end` gets a hard-coded `1`. A third state
already exists downstream (`total_pending`, `Pending: {n}`), but
`test_runner_single.spl:452` hard-wires it to `0` and the `simple-bdd-v1`
evidence format has no pending field with an exact-content check — so this needs
an evidence `v2`, not a one-line flip.
