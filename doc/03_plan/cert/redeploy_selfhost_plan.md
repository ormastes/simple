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
