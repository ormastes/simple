# `simple build bootstrap` accepted planner flags and started a real build

- **Filed:** 2026-08-18
- **Status:** FIXED (CLI routing + gate message), guarded
- **Severity:** high — the documented UX did the opposite of what it promised

## Symptom

`scripts/bootstrap/bootstrap-from-scratch.sh` (admission gate) printed, verbatim:

```
bootstrap-policy-error: reason-receipt-required; run 'simple build bootstrap --bootstrap-reason=<typed-reason> --bootstrap-receipt=<path>'
```

Following that instruction exactly:

```
bin/simple build bootstrap --bootstrap-reason=self-host-convergence-check --bootstrap-receipt=<path>
```

did **not** plan a receipt. Reproduced 2026-08-18 against
`bin/release/x86_64-unknown-linux-gnu/simple` (59621024 bytes, 2026-08-17
20:28:24):

```
Bootstrap pipeline starting...
=== Stage 1: Compile with seed compiler ===
  Running: .../simple native-build --source src/app --entry-closure --strip --threads 1 --timeout 180 --entry src/app/cli/bootstrap_main.spl -o bootstrap/stage1/simple --backend=llvm-lib
error: native-build worker exited with code 143.   # SIGTERM from the 180s budget
Stage 1 FAILED
RC=1
```

No receipt file was created. Earlier the same failure surfaced as
`error: native-build worker timed out after 180s before producing a binary.`

## Root cause

`src/compiler_rust/driver/src/cli/commands/misc_commands.rs`, `handle_bootstrap`:
the option loop recognised only `--backend=`, `--output=`, `--seed=` and had **no
else branch**. Every other flag — including both flags the gate message tells
users to pass — was silently dropped, and control fell straight through to
`compile_stage`, a real 3-stage native-build.

Note the pure-Simple CLI (`src/app/build/cli_entry.spl:63-64`) already routed
`bootstrap` to `plan_bootstrap_authorization`. Only the Rust seed — which is what
`bin/simple` currently is — was wrong. The gate message was also incomplete: the
planner additionally requires `--parent-compiler-sha256`,
`--runtime-snapshot-sha256`, `--planner-source-closure-sha256`, `--planner-sha256`.

## Fix

1. `misc_commands.rs` `handle_bootstrap`: any planner flag routes the whole argv
   to the pure-Simple planner via a new
   `delegate_to_bootstrap_receipt_planner()` (`<self> run
   src/app/build/bootstrap_receipt_main.spl <args...>`, exit code propagated).
   Out-of-process on purpose — the planner is documented as independent of the
   native-build CLI closure. `--help` now lists the planner flags.
2. Same function: unknown flags now **fail closed** (exit 64) instead of being
   dropped.
3. `scripts/bootstrap/bootstrap-from-scratch.sh:301-304`: the message now names
   `simple run src/app/build/bootstrap_receipt_main.spl` with the full flag set.
   This form works with the **currently deployed** seed (verified: receipt
   written, `bootstrap-plan: execution=not-attempted`, RC=0); fix (1) makes the
   older wording work too once the seed is next rebuilt.

Fix (1)/(2) are source-only in this change — `bin/simple` was deliberately **not**
rebuilt (≈15 lanes depend on the current binary), so they take effect at the next
seed build. Fix (3) is effective immediately, which is why the message was
changed rather than left to depend on a rebuild.

## Guard

`scripts/check/check-bootstrap-receipt-instruction.shs` — extracts the
recommended command from the gate script's own message, substitutes the
placeholders, runs it, and asserts (1) the named entry exists, (2) exit 0,
(3) a non-empty receipt appears at the user-supplied path, (4) no bootstrap stage
was started. `PASS — <n> assertion(s) checked` / `FAIL` / `ERROR — nothing was
checked`; `--selftest` is fatal (4 fixtures). Rewording the advice without making
the new advice work re-fails the guard.

Not touched, per lane split: `bootstrap_receipt_planner.spl`,
`bootstrap_policy.spl`.
