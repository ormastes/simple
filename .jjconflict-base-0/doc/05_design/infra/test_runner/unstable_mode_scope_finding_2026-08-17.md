# `unstable_mode`: what it actually controls, and what it should mean

Status: FINDING CONFIRMED (independently re-verified by lane ISOLATION, 2026-08-17)
Scope: `src/lib/nogc_sync_mut/test_runner/**`, `src/app/test_runner_new/test_runner_main.spl`

## 1. The audit finding, re-verified

The requirements audit reported that `unstable_mode`'s only real behavioural
effect today is forcing `fail_fast = false`. **That holds.** Verified by an
exhaustive grep for `unstable_mode` across `src/**` (`.spl` and `.rs`).

### Complete read-site table

| file:line | what it is | what it controls |
|---|---|---|
| `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl:94` | field decl `unstable_mode: bool` | storage only |
| `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl:95` | field decl `unstable_mode_set: bool` | storage only (explicit-flag tri-state) |
| `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:327-332` | `--unstable` / `--no-unstable` parse | WRITES the two fields |
| `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:629-630` | struct construction | WRITES |
| `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:156` | flag recognised in the known-arg list | argument validation only |
| `src/app/test_runner_new/test_runner_main.spl:194-200` | resolve explicit flag vs `SIMPLE_BOOTSTRAP=1` default | WRITES the effective value |
| `src/app/test_runner_new/test_runner_main.spl:201,204` | `"Unstable mode: ON/OFF (<origin>)"` banner | printing only |
| **`src/app/test_runner_new/test_runner_main.spl:205-207`** | `if updated_options.unstable_mode: fail_fast = false` | **the ONLY behavioural effect in the entire tree** |
| `src/compiler_rust/driver/src/cli/help.rs:351` | Rust unit test asserting help text | docs test only |
| `src/compiler/80.driver/driver_build/parallel.spl:121` | `ParallelBuildConfig.unstable_mode(...)` static ctor | unrelated name; a config factory. Its consumer `build_supervised()` (`parallel.spl:693`) has **ZERO callers** — build-side isolation is dead code |

There is **no** other conditional on the flag. `test_runner_execute.spl` does
not reference `options.unstable_mode` at all (its single textual hit, line 61,
is a comment citing `.spipe/unstable_test_mode/state.md`).

### Test-side isolation is unconditional — confirmed

Every execution variant — `run_test_file_interpreter` (:186),
`run_test_file_smf` (:288), `run_test_file_native` (:807), and the
`process_run_with_limits_bounded` branches that precede each — spawns the spec
in its own child process on **every** path, both branches of the
`max_mem_gb`/`max_procs` conditional included. Nothing gates it. It predates
this work.

So the delivered mode is: **classification (real) + run-to-end (real) +
isolation (real on the test side, but not attributable to the mode; absent on
the build side).**

## 2. Recommendation: (b) — always-on isolation is CORRECT; redefine the mode

**Recommendation: keep isolation unconditional, and redefine `unstable_mode` in
the requirement doc as "classification + run-to-end", stating plainly that
per-spec process isolation is an unconditional property of the runner rather
than a mode feature.**

Reasoning, and why this is not a rationalisation of the status quo:

1. **Isolation is a precondition of the outcome contract, not a peer of it.**
   The settled classes OK/ERROR/CRASHED/TERMINATED/TIMEOUT/NOT_RUN are derived
   from a *child process's* exit code and `limit_type`. With no child there is
   no 137, no 143, no timeout kill — CRASHED and TERMINATED become
   unrepresentable. A mode whose headline feature is classified outcomes cannot
   sit on top of an execution path that is only sometimes able to observe them.

2. **Gating it would be a pure regression.** Option (a) makes non-unstable runs
   *worse at telling the truth*: a segfaulting spec would take the runner down
   instead of being reported as CRASHED, and every interactive user would
   inherit that. The supposed upside is speed, and it is unmeasured — nobody has
   shown that in-process execution is meaningfully faster here, and the runner
   would additionally need an in-process execution path that does not currently
   exist. That is a large, risky build to obtain a worse guarantee.

3. **The honest gap is elsewhere.** The requirement asked for "separate process
   for build AND test". The test half is already satisfied unconditionally; the
   *build* half is genuinely missing — `build_supervised()` has zero callers.
   Framing the shortfall as "isolation isn't gated" misdirects effort at the
   half that already works, away from the half that does not.

Consequently the mode's honest definition is: **`unstable_mode` = run to the end
of both lists (`fail_fast = false`) with classified outcomes and a visible
banner.** Isolation should be documented as an unconditional runner invariant.

## 3. What was and was not changed

- **Changed:** a header comment block in
  `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl` stating that
  per-spec isolation is unconditional and *why* it is not gated, so the next
  reader does not re-derive this or "fix" it by adding a gate. Comment only;
  zero behavioural delta (no ablation applicable).
- **Deliberately NOT changed:** `doc/02_requirements/infra/supervised_test_runner.md`
  (owned by the audit lane — it needs the (b) redefinition applied, but that is
  the audit lane's edit, not this one), `test_runner_main.spl`,
  `test_runner_args.spl`, `test_runner_types.spl`, and
  `src/compiler/80.driver/**`.
- **Deliberately NOT done:** no gate was added. Option (a) would change default
  behaviour for every interactive user and is the user's call, not a lane's.
- **No new spec was written.** A `unstable_mode_effect_*` spec would assert only
  that `fail_fast` flips — a one-field assignment already visible at
  `test_runner_main.spl:205` — and could not observe isolation, since isolation
  is unconditional and therefore has no contrast case to test against.

## 4. Open item for the requirement owner

Build-side isolation remains unimplemented: `build_supervised()`
(`src/compiler/80.driver/driver_build/parallel.spl:693`) and
`ParallelBuildConfig.unstable_mode()` (`:121`) are both uncalled. Either wire
them or record the requirement as partially met — do not let the working test
half imply the build half exists.
