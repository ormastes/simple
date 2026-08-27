# A full-suite run aborts before executing anything: `variable mcdc_dynamic_probe_controller_load_builtin_current_owner not found` (2026-08-26)

**Status:** OPEN. Found running the full suite from a clean worktree at `b2cbf73988f` with the
2026-08-26 01:16 deployed seed.

## Symptom

`bin/simple test --no-cover-check` enumerates the tree, completes session setup, and then dies
with a single semantic error, having executed **zero** tests:

```
Running 15552 test file(s) [mode: interpreter]...
Self-protection enabled (stops when free CPU < 25.0% AND free RAM < 25.0%)
  Max memory per test: 16GB
Change-detection cache bypassed (--clean)
Session setup: 60303ms

error: semantic: variable `mcdc_dynamic_probe_controller_load_builtin_current_owner` not found
```

There is no `Results:` line and no `ABORTED BEFORE EXECUTION` block, so per
`.claude/rules/testing.md` the outcome of all 15,552 files is **UNKNOWN, not failed**. Note this
is a *different* failure shape from the documented preflight abort: that one prints an explicit
`ABORTED BEFORE EXECUTION` banner naming the gate and its bypass. This one just stops. A run that
dies without either a results line or an abort banner is the worst of both — it looks like a
crash and carries no instruction.

## What is ruled out

- **The symbol exists.** `src/lib/nogc_sync_mut/mcdc/dynamic_probe.spl:225`, `pub fn`.
- **Both import spellings resolve.** `use std.nogc_sync_mut.mcdc.dynamic_probe.{…}` and
  `use std.mcdc.dynamic_probe.{…}` each load and call cleanly from a file inside the project,
  at top level as well as inside `fn main()`.
- **Not the generated MC/DC prelude's import, as first suspected.**
  `test_executor_parsing.spl:793/815` emit that `use` and call, but only when `mcdc_enabled`,
  which is `SIMPLE_MCDC_MODE in {on, dynamic}` (`test_runner_execute.spl:843`,
  `test_executor_parsing.spl:772`). The failing run had that variable unset. Those `lines.push(...)`
  occurrences are string literals and resolve nothing by themselves.
- **Not the spec that imports it.** `test/01_unit/lib/mcdc_probe_protocol_spec.spl` runs to a
  verdict on its own (`9 total, 2 passed, 7 failed` — its own failures are a separate matter).
- **Not single-spec MC/DC.** `bin/simple test <one spec> --mcdc --keep-artifacts` passes 3/3.
- **Not an out-of-project path effect.** A probe under `/tmp` warns
  `stdlib import … resolves from the project stdlib roots only` but still returns a value; the
  same probe inside the project is silent. Neither produces this hard error.

## MECHANISM (2026-08-27): co-compiled duplicate definitions, and the directory-only entry point

The same run that aborts emits **11** duplicate-definition warnings, including:

```
warning: public function `discover_test_files` has 2 co-compiled definitions with 2 differing
         signatures ((text)->[text] vs (text,TestOptions)->[text]); JIT call sites resolve ...
warning: public function `env_get` has 4 co-compiled definitions with 2 differing signatures
warning: public function `mcdc_condition_key` has 2 co-compiled definitions with 2 differing signatures
warning: class `Trace32Adapter` has 2 co-compiled definitions across 2 modules; the interpreter
         resolves class members by NAME across modules ...
```

`discover_test_files` is **the directory-expansion function** — a directory target calls it, a file
target does not. That lines the mechanism up exactly with the discriminator above: the failing path
is the one that goes through a symbol which exists twice, with *different signatures*, in
co-compiled modules. `mcdc_condition_key` being doubled the same way puts the MC/DC machinery in
the same blast radius as the symbol named in the abort.

The interpreter resolving members **by name across modules** is a known defect class in this repo,
and these warnings are it firing in the test runner's own dependency graph.

Likely source of the duplication: facade modules that re-export a sibling family wholesale, e.g.
`src/lib/nogc_async_mut/test_runner/test_runner_types.spl:1` is
`export use std.nogc_sync_mut.test_runner.test_runner_types.*`. A wildcard re-export makes both
copies co-compiled, so every name in the family exists twice.

**Not fixed here.** De-duplicating those module families is a real refactor with wide blast radius
across the test runner, and doing it blind — while `bin/simple test` cannot run to give a
regression signal — would be reckless. The right order is: fix the duplication (or make the
interpreter's cross-module resolution deterministic), then re-run this repro, which is now a
two-second check rather than a 15,000-file run.

## DISCRIMINATOR FOUND (2026-08-27): directory target aborts, file target does not

The same single spec, same binary, same tree:

```
bin/simple test test/zz_mini            --no-cover-check   ->  error: ... not found   (ABORTS)
bin/simple test test/zz_mini/foo_spec.spl --no-cover-check ->  Results: 1 total       (RUNS)
```

A **two-file** directory reproduces it, so this is fast to iterate on — no 15k-file run needed.
The trigger is the *target being a directory*, not batch size and not any particular spec: the
directory used here contains ordinary compiler specs with no MC/DC reference at all.

That narrows it to whatever the directory path does differently from the file path before the
per-file loop — discovery/expansion and the session setup that follows it. It also explains the
one fact that previously did not fit: a concurrent session's run was executing specs normally
because of how it invoked the runner, not because the defect was intermittent.

## Earlier: no discriminator, and one false lead recorded

An earlier draft of this record claimed that adding `--no-mcdc` avoided the abort, and concluded
MC/DC must be active by some non-env route. **That was wrong.** `--no-mcdc` is not a `test`
option at all — the run rejected it instantly with `Error: unknown option: --no-mcdc` and never
started, which was misread as "it got further". (`--no-mcdc` exists in
`src/compiler/00.common/config.spl:200`, the *compiler* CLI, not the test runner.) There is
therefore no evidence MC/DC is involved beyond the symbol named in the message, and the
"ruled out" list above stands unchanged.

Recording the false lead rather than deleting it: the failure mode is a run that dies so early it
resembles a run that progressed, which is exactly how this class hides.

## Scope: ANY multi-file run, and it is PRE-EXISTING

Not full-suite-specific. `bin/simple test test/01_unit/compiler --no-cover-check` (2253 files,
**zero** of which reference MC/DC) aborts identically, right after `Session setup`, before a
single per-file PASS/FAIL line. A single spec always succeeds — the same spec that is in that
directory passes 3/3 on its own, including with `SIMPLE_MCDC_MODE=on --keep-artifacts`.

**Proven independent of the 2026-08-26 seed redeploy.** The obvious worry was that registering
`@always_inline` (which made these runs get this far at all) introduced this. It did not: with
the decorator stripped from all 81 files that carry it, the **pre-redeploy** binary
(`simple.pre-alwaysinline-20260826`) reaches the identical
`variable mcdc_dynamic_probe_controller_load_builtin_current_owner not found`. The defect was
simply hidden behind the earlier abort — fix one startup blocker and the next one surfaces.

Corroboration from a concurrent session: its `test/01_unit` run, started 00:36 on the old binary
*before* the redeploy, is executing specs normally with zero occurrences of this error — because
it never got past... no: it did get past, which is the one piece that does not fit and is worth
chasing. That run and these differ in tree (shared vs. clean worktree) and invocation, so the
difference is a live lead, not an explanation.

## Additional facts

- **MC/DC is on even with the env unset.** `test_runner_config.spl:249` calls
  `env_set("SIMPLE_MCDC_MODE", effective_mcdc_mode)` from `resolve_mcdc_mode_for_profile(...)`,
  so the two `mcdc_enabled` computations that read that variable see it set by the runner itself.
  This is why the earlier "MC/DC is not enabled here" reasoning was wrong.
- **Not the import spelling.** The prelude's `use std.nogc_sync_mut.mcdc.dynamic_probe.{…}` is
  the odd one out among its siblings, which use short forms. Rewriting it to
  `use std.mcdc.dynamic_probe.{…}` changes nothing — same abort.
- **No wrapper is ever written.** With `--keep-artifacts`, no fresh
  `.sspec_wrapped_entry_*.spl` appears under the target directory, so the run dies at or before
  the first file's wrapper generation, not while compiling a generated wrapper.
- The per-file loop begins immediately after the `Session setup: Nms` line
  (`src/app/test_runner_new/test_runner_main.spl:392-409`), so the failure is on the first file.

## Impact

`bin/simple test` with no flags cannot produce a verdict for the tree. Any session reporting full
suite results must be passing flags, using a different entry point, or reading a run that never
executed. No workaround is known yet: the only flag tried, `--no-mcdc`, is not a valid `test` option. Directory-scoped runs (e.g. `bin/simple test test/01_unit`) do reach execution, so a verdict can be assembled from sequential per-directory runs.

(The `--no-cover-check` half is separate and benign — a documented preflight gate fires because
2113 system tests lack `# @cover`, and it announces itself and its bypass properly.)

## Where to look

Whatever sets MC/DC on for a whole-suite run when `SIMPLE_MCDC_MODE` is unset, then
`build_coverage_wrapper` (`test_executor_parsing.spl:771`) and the prelude it emits at :786-815.
The mechanism was not pinned; everything above is what was measured, not inferred.
