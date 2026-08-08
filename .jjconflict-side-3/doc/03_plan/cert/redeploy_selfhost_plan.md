# Stage4 Redeploy — Deferred Plan (pure-Simple self-host path)

**Status: DEFERRED by user directive (2026-07-05).** Redeploy is not being pursued
interactively; this doc captures the details so it can be executed later. The
deployed `bin/release/x86_64-unknown-linux-gnu/simple` is clean and stays as-is.

## Why redeploy matters
~130 correct pure-Simple source fixes are **frozen behind redeploy** — they are on
`main` but not in the deployed binary. Notable frozen fixes: the Result/Option
payload-index fix (`938a4eb`, so `Ok(42).unwrap()` still returns `5` on the deployed
binary), the warn-only type-checker wiring (`a61d6971`), and the whole
deep-recheck P1/P2 batch (see `doc/08_tracking/bug/deep_recheck_2026-07-05.md`).

## The wall (root cause — evidence-backed, two hypotheses falsified this session)
Building stage4 from the **144 MB Rust seed** (`src/compiler_rust/target/bootstrap/simple`)
via cranelift produces a miscompiled interpreter: `-c "val x=5; print(x)"` and
struct field access fail, gate scores 4/14.

- **FALSIFIED:** "seed `BoxInt <<3` mangles enum heap-handles" — a full-MIR audit
  (all 5783 fns) found zero heap-fed BoxInt in the interpreter.
- **FALSIFIED:** "global-by-name struct/field registry collision" — `layout.rs`
  `get_by_name`/`name_to_type` are dead code; a **uniquely-named** `struct P(x:5).x`
  still fails with `<no such field: x>`.
- **CONFIRMED:** the seed's cranelift mis-lowers `Dict<text,Value>`/enum-payload ops
  that traverse the **ANY-erased enum channel** (the #103/#107/#117 class). The stage4
  interpreter resolves struct fields at runtime via a name-keyed `Dict<text,Value>`
  (`src/compiler/70.backend/backend/interpreter.spl:249`); the seed corrupts that
  Dict-of-enum. `Value.Object` survives (fields in `ObjectStore` by handle, off the
  ANY channel); `Value.Struct` (inline-Dict payload) is corrupted.
- **The wall is SEED-cranelift-only.** The pure-Simple codegen
  (`src/compiler/70.backend/`, used by deployed `bin/simple`) is clean — `bin/simple`
  runs every failing repro correctly.

## The redeploy path (when un-deferred): pure-Simple SELF-HOST
Do **not** keep fixing the seed (2 inert lanes this session, 6+ prior iterations).
Instead build stage4 with **`bin/simple`'s own clean codegen**:

```bash
bin/simple native-build --source src/compiler --source src/lib --source src/app \
  --entry src/app/cli/main.spl --cache-dir <fresh> -o <out>   # adapt flags to real interface
# or: scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple --deploy   (see .claude/rules/bootstrap.md)
```

Then gate: `scratchpad/redeploy_gate.sh <out>` (14 checks; deployed `bin/simple`
scores ~12–14, a seed-cranelift stage4 scores 4). On PASS: back up the current
deployed binary, `cp <out> bin/release/<triple>/simple.new && mv` it into place,
**re-gate via `bin/simple`**, restore the backup on any failure.

### Open feasibility question (the deferred work)
A prior self-host run was ~39 min at 0-cache with an "interpreted worker" and was
killed inconclusive. Before executing redeploy, resolve: does `bin/simple native-build`
use a compiled fast-path (vs interpreted worker), is `--cache-dir` incremental across
runs, and is there any self-host **feature gap**? If the full build is tractable
(< ~40 min) and gate-passes, redeploy is one clean build away. If it's perf-blocked,
the deferred task is to make `bin/simple` native-build fast enough (caching/perf).

### 2026-07-06 update: fix correctness before speed

Current local research shows the redeploy path is blocked by correctness first,
not by the shell script scheduler. `bootstrap-from-scratch.sh` now passes
`--threads`, but Stage 2 still fails before producing a compiler, then Stage 3
has no executable and Stage 4 falls back to the seed. The active Stage 2 fix is
tracked in `doc/08_tracking/bug/bootstrap_stage2_empty_mir_bodies_2026-07-05.md`:
bootstrap same-module `Var(symbol)` calls must lower to named function-pointer
calls with the correct bootstrap return types instead of invalid numeric callees.

The observed speed issue is real but separate. `ParallelBuilder.build()` still
executes each ready chunk item serially inside one native-build worker, so
`--threads 16` leaves one hot `simple-main` thread and idle service threads.
Do not spend more time tuning `--jobs` until Stage 2 is green. After correctness
is fixed, parallelism should be implemented as process-level per-module work
with serialized inputs/outputs; do not wrap the current shared driver context in
threads without proving backend state safety.

## Gate hygiene
`scratchpad/payload_check.spl` / `qmark_check.spl` were restored to use **custom
enums** (`enum Payload{Present(int),Absent}` etc.) — built-in `Result`/`Ok`/`Err`/`?`
are themselves broken on the deployed binary (the frozen `938a4eb` fix), so they
cannot be used as gate discriminators until after redeploy.

**2026-07-06 supersession:** the gate + fixtures were migrated from ephemeral
/tmp to **tracked** `scripts/check/cert/redeploy_gate/` (runner
`redeploy_gate.shs` + 10 fixtures, 12 checks, pushed to origin). The tracked
fixtures target the *candidate rebuilt* binary, so `Ok(42)→42` IS the correct
#109 discriminator there (the broken deployed binary prints 5); the custom-enum
caveat above only applied to gating the *frozen deployed* binary.

### 2026-07-06/07 update: stage-4 failure taxonomy — all four classes root-caused

Chronology of stage-4 CLI build failures, each with evidence and disposition:

| # | Error class | Count | Root cause | Status |
|---|-------------|-------|-----------|--------|
| 1 | LLVM IR "Incorrect number of arguments" on `mcall_direct` | 545× | seed llvm-lib method-call lowering mis-counts self param | **FIXED** — functions.rs indirect-call fallback (on main, `ba387415d7f`); post-fix logs read 0 |
| 2 | LLVM IR "Call parameter type does not match" (`rt_dir_create`) | 25× | extern C-ABI signature registration mismatch | **FIXED** — same commit, forced C-ABI indirect call; post-fix logs read 0 |
| 3 | "Use explicit exports instead" on `export use module.*` | 60 sites | **RED HERRING** — `ErrorHintLevel::Warning`, exit 0 (module_system.rs:563 + passing unit test). Never fatal | no action; do NOT "fix" |
| 4 | Silent death mid-build, no error line | 3+ runs over 2 days | **RC=134 SIGABRT: `thread 'simple-main' has overflowed its stack`** after parser errors at `src/compiler/backend/target_presets.spl:318:101` — seed parser fails on `mut` **parameter** syntax (`fn f(preset: T, mut options: CompileOptions) -> ...`), then error-recovery recurses unboundedly | **OPEN — the actual redeploy wall.** Fix design: `doc/05_design/compiler/bootstrap/stage4_redeploy_failure_and_fix_design.md` |

Evidence for class 4 (first instrumented run, 2026-07-06 11:58→14:08, RC
captured; prior runs died without recording an exit code):
`[parser_error] line 318:101: unexpected token in expression: ':'` on the
`-> CompileOptions:` tail of a `mut`-param fn signature, followed by
`fatal runtime error: stack overflow, aborting`. `mut` params appear in ≥5
compiler .spl files (60.mir_opt ×3, 70.backend ×2), so skipping one file is not
a fix. Secondary hazard found: BOTH `src/compiler/backend/target_presets.spl`
(failing path) and `src/compiler/70.backend/target_presets.spl` exist —
duplicate-module risk (see #41 class), must be reconciled during the fix.

Operational hazards confirmed while diagnosing (all can kill a 2h stage-4 run):
- `kill_simple_monitor` kills `native_build_main` at **RSS ≥ 24 GB** (3 kills
  06:33–07:00 @30 GB). Mitigation: `--threads 8`, watch RSS.
- Un-instrumented runs die silently (no RC, no signal in logs). Mandate: every
  stage-4 run wraps in `sh -c '...; echo RC=$?'` with stderr preserved.

### 2026-07-07 (evening) — EMPIRICAL: parser wall fixed, but stage2 self-host still fails

Two facts were proven this session, both by running to completion instead of guessing:

1. **The parser recursion wall (RC=134) is FIXED.** A fresh seed built with the
   `MAX_PARSE_RECURSION_DEPTH=512` guard ran the full stage4 build for **6h with
   no stack overflow** — the SIGABRT is gone. The guard works.
2. **But the seed-interpreted stage4 path is PERF-DEAD.** That same 6h run
   (`--timeout 21600`, `--threads 8`) **timed out before emitting a binary**. The
   interpreted worker cannot compile the whole compiler in 6h. Conclusion:
   redeploy is impossible via the seed; it REQUIRES stage2→stage3 self-host to
   succeed (so stage4 is built by a *compiled* pure-Simple compiler, not the seed).

**Stage2 self-host does NOT pass on `main` (tip `14a35ab`).** The latest stage2
log (`build/bootstrap/logs/x86_64-.../stage2-native-build.log`, 07-07 05:35)
lowers `bootstrap_main.spl` fine (`bootstrap-functions:count 6`) then lowers
**two more modules with `functions:count 0`** → empty LLVM IR → `llc failed
during bootstrap` → worker exit 1. Stage3 log is 0 bytes (never ran); stage4
fell back to the seed. This is the "empty MIR bodies" bug
(`doc/08_tracking/bug/bootstrap_stage2_empty_mir_bodies_2026-07-05.md`) — still
open despite the `speed up pure Simple bootstrap` / `link bootstrap stage2 from
fresh MIR` commits.

**A parallel lane is actively fixing this.** The main WC has 27 uncommitted files
(`driver_bootstrap.spl`, `driver_aot_output.spl`, `_MirToLlvm/*`, mir_opt, +3 new
specs `bootstrap_decl_count_slot_spec` / `bootstrap_context_mir_source_spec` /
`bootstrap_llvm_entry_symbol_source_spec`) — exactly the empty-MIR/decl-count
path. Do NOT edit those files in the main WC (collision). Next action is decided
by whether that in-progress diff fixes stage2 (validate in an isolated worktree
with a cheap stage2-only repro) — NOT by re-running the seed build, which only
reconfirms the 6h timeout.

### 2026-07-07 (evening, cont.) — FRONTIER MOVED: stage2 fixed, stage3 SIGSEGV

Validated the lane's in-progress fix by running a full pure-Simple bootstrap on a
**frozen snapshot** (isolated worktree @ `14a35ab` + symlinked seed + rsynced the
20 changed `src/**.spl` files). Result in ~76s (monitor killed the seed-fallback):

- **Stage 2 PASSES** ✅ — seed → `bootstrap_main.spl` now compiles + links a real
  20 KB stage2 binary (`llc-done`, `llc-object`). The string-globals fix cleared
  the `@.str.0` wall for real.
- **Stage 3 self-host SIGSEGVs** ❌ (exit 139) → falls back to seed for stage 4.
  Crash symbolized on the stage2 binary: `SIGSEGV at address (nil)` in
  **`__simple_main`** (frame `0x202024`, = `__simple_main`+0x34; the other frame
  `0x202214` is just `_spl_crash_handler`). The stage2 binary null-derefs at entry
  on ANY invocation, incl. `--version`.

**Root of the stage3 crash = the lane's mid-edit `main`→`__simple_main` rename.**
Their uncommitted `_MirToLlvm/core_codegen.spl` adds
`val fn_name = if fn_.name == "main": "__simple_main" else: fn_.name` to the
**bootstrap** codegen path. `__simple_main` normally runs only after the C `main`
wrapper (`backend/entry_point.spl`) calls `spl_init_args`; the bootstrap-path
rename produces a `__simple_main` whose arg-init/C-main wiring is not yet complete,
so it derefs a nil args global at entry. This is incomplete-fix churn, not a
permanent wall — do NOT fix it here (collision with the active lane).

**Disposition:** redeploy is gated on the lane finishing the `__simple_main`
entry wiring and committing. Re-validation is armed: rerun
`scratchpad/frozen_bootstrap.sh` (reuses the worktree, re-copies the latest
`.spl`, ~90s to the stage2/stage3 frontier). When stage3 stops SIGSEGVing, the
same script builds stage4 + gates it; deploy then needs backup + user go-ahead.

### Execution plan (2026-07-07, per user directive)

1. **Docs first** (this update + the design doc) — DONE with this commit.
2. **Fix BOTH sides in an isolated worktree** (do not disturb main WC):
   - Rust seed: bound parser error-recovery recursion (fail gracefully with
     file:line context, never SIGABRT); accept `mut` param syntax if cheap.
   - Pure-Simple: make the 5+ `mut`-param signatures seed-compatible
     (mechanical `var` local rebind) ONLY if seed-side `mut`-param support is
     not cheap; language-level `mut` params stay valid for the self-hosted
     compiler. Reconcile the duplicate target_presets.spl.
3. **Bootstrap pure-Simple only** (`bootstrap-from-scratch.sh`, NO
   `--full-bootstrap` — reuse the existing fixed seed; per user, a passing
   seed+full bootstrap was already achieved by another lane).
4. **Gate**: `scripts/check/cert/redeploy_gate/redeploy_gate.shs <candidate>` —
   12 behavioral checks; deploy consideration only on GATE all-PASS.
5. **Deploy** (user go-ahead required): backup current
   `bin/release/x86_64-unknown-linux-gnu/simple` → `.bak-<date>`, swap via
   `cp` to `.new` + `mv` (avoids "Text file busy"), immediate smoke + gate on
   the deployed path, instant rollback on any regression.
6. **Close-out**: #45/#99/#112 verify on the redeployed binary (gate checks
   cfg-arch-dispatch-a/b, class-in-array-mutation=777 interpret-mode,
   enum-payload=42); update ACTIVATION_MANIFEST + this doc.
