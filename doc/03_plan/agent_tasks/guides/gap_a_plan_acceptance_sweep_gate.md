# Guide A2 — harden the LANDED plan-acceptance sweep gate (do not create a second one)

Owner: one sonnet-class agent. Depends on Guide A1 landing first (the sweep
needs a runner that executes children). Follow literally.

## What already exists (landed 2026-09-05 while this plan was written — probe it first)

- `scripts/check/check-plan-acceptance-swept.shs` — asserts (1) it is wired
  as a push-tier row + dispatch arm, and (2) every spec under
  `test/03_system/plan_acceptance/` loads and runs (`SPEC FILE VERDICT ...
  executed=N` with N > 0). 8-fixture `--selftest`. Manifest row
  `push-plan-acceptance-swept` (push, advisory, LAST row by design).
- Its one current offender: `spipe_knowledge_base_spec.spl` — `app.spipe.kb`
  is an unresolved import, `executed=0`. Not yours to edit (plan item A4).

Do NOT create `check-plan-acceptance-sweep.shs` or any new manifest row for
the same purpose. Everything below is an EDIT to the landed script.

## What it still lacks against the Gap A property (add each, with a selftest fixture)

1. **Crash-vs-assertion distinction.** Today `executed>0` is the only load
   check. Add: for every spec that carries `# @tag:in-development`, the sweep
   output must show EITHER an `IN-DEVELOPMENT SKIP` line whose relayed
   `SPEC FILE VERDICT` has `executed>=1` and `failed>=1` (a neutralised real
   assertion failure) OR an `UNEXPECTED PASS` line. A tagged spec that is
   neutralised with `executed=0` is a LOAD FAILURE, not a neutralised
   assertion — report it as an offender under a separate label
   (`load-failure-neutralised:<name>`), because that is exactly the shape
   Gap A was hiding behind.
2. **`E1034` → ERROR.** Any `E1034` in the captured sweep output is
   `ERROR — nothing was checked (imports degraded to shims)` exit 2.
3. **Bootstrap-tier row.** Add
   `plan-acceptance-swept, bootstrap, false, automated, "sh scripts/check/check-plan-acceptance-swept.shs", "bootstrap sweeps test/03_system/plan_acceptance under the in-development contract"`
   to `config/check/must_check_gates.sdn` so a bootstrap run exercises the
   same script. Then `sh scripts/check/check-guard-wiring.shs` must PASS.
4. **Selftest fixtures** for 1 and 2: write fixture sources with `printf`;
   NEVER put `{...}` inside a Simple text literal (it is interpolation —
   measured: `"use std.spec.{step}"` renders `use std.spec.<fn:step>`). Use
   `use std.spec.*`. Fixtures: tagged failing (`expect(1).to_equal(2)`) must be
   classified neutralised-assertion; a tagged file that fails to load must be
   classified `load-failure-neutralised`; an output containing `E1034` must
   ERROR.

Exit status of the runner is read DIRECTLY into a variable on the next line
(never through a pipe).

## Acceptance

- `sh scripts/check/check-plan-acceptance-swept.shs --selftest` → selftest
  PASS including the three new fixtures.
- `SIMPLE_BINARY=$PWD/src/compiler_rust/target/debug/simple sh scripts/check/check-plan-acceptance-swept.shs`
  → last line names 35+ specs and lists every offender by label; no
  `load-failure-neutralised` offender other than those the plan already
  records (A4).
- `sh scripts/check/check-guard-wiring.shs` → PASS.

## Checkbox rule

Tick plan item A2 ONLY when the three commands above give those results, and
append `— verified <last stdout line of each>, <date>`.
