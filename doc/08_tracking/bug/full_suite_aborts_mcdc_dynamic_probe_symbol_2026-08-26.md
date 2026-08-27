# A full-suite run aborts before executing anything: `variable mcdc_dynamic_probe_controller_load_builtin_current_owner not found` (2026-08-26)

**Status:** OPEN. The original operator report says this was found in a clean worktree at
`b2cbf73988f` with the 2026-08-26 01:16 deployed seed. No binary digest or retained worktree
transcript makes that binary provenance independently verifiable.

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

## Early operator-reported probes

- **The symbol exists.** `src/lib/nogc_sync_mut/mcdc/dynamic_probe.spl:225`, `pub fn`.
- **Both import spellings resolve.** `use std.nogc_sync_mut.mcdc.dynamic_probe.{…}` and
  `use std.mcdc.dynamic_probe.{…}` each load and call cleanly from a file inside the project,
  at top level as well as inside `fn main()`.
- **Historical false reasoning — not a ruled-out item.** An earlier draft argued that the generated
  MC/DC prelude could not be involved because `SIMPLE_MCDC_MODE` was unset on process entry. That is
  false: `resolve_mcdc_mode_for_profile(...)` selects `on` for an unset mode at the normal/default
  profile, and `propagate_env_vars` writes that effective value back before the later
  `mcdc_enabled` checks. The `lines.push(...)` occurrences are string literals at runner load time,
  but the generated prelude is active in the reported unset/default run.
- **Reported importing-spec result.** `test/01_unit/lib/mcdc_probe_protocol_spec.spl` reached a
  verdict on its own (`9 total, 2 passed, 7 failed` — its own failures are a separate matter).
- **Reported single-spec MC/DC result.** `bin/simple test <one spec> --mcdc --keep-artifacts`
  passed 3/3 in the cited run.
- **Reported path probe.** A probe under `/tmp` warned
  `stdlib import … resolves from the project stdlib roots only` but still returns a value; the
  same probe inside the project is silent. Neither produces this hard error.

## Evidence boundary for the 2026-08-27 experiments

The immutable original report commit is
`5c88fb433fa00d8211262d8a6cf24fd2848aafb1`; its parent is
`72a466dd6d3bbe02b6fd65ebac65458a19efa286`. The commit message says the experiments below used a
clean `origin/main` worktree, but it does **not** retain the tested HEAD, binary digest, raw command
transcripts, scratch-fixture contents, duplicate-rename patch, or MC/DC waiver values. The source
facts about wrapper naming and cleanup described below are directly inspectable at the immutable
parent with:

```
git grep -n 'simple_cov_' 72a466dd6d3bbe02b6fd65ebac65458a19efa286 -- \
  src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl
git grep -n 'not options.keep_artifacts' 72a466dd6d3bbe02b6fd65ebac65458a19efa286 -- \
  src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl
```

The abort strings and refutation results below are operator-recorded observations, not immutable
reproduction evidence. They should be re-run with a committed fixture or an evidence bundle before
being used to close this bug.

## Reported refuted hypotheses (2026-08-27) — read this before forming a new one

Four refutations were reported. Check the evidence boundary above before relying on or repeating one:

| # | hypothesis | test | result |
|---|---|---|---|
| 1 | stale `.smf` files shadow the source | parked all 8 under `gpu_runtime/` | no change |
| 2 | a same-named class method collides | renamed `BrowserNavigator.gpu_available` | no change |
| 3 | duplicate co-compiled `discover_test_files` | renamed the daemon's copy so the collision is gone | no change |
| 4 | the deployed binary predates the symbol | built a seed from the CURRENT `origin/main` and re-ran | **no change** |

Hypothesis 4 deserves a note because it looked airtight: the second failure mode is
`unknown extern function: rt_process_run_owned_observed_bounded_value`, and that symbol *is*
registered at `src/compiler_rust/common/src/runtime_symbols.rs:1901`, which reads exactly like a
binary that predates its registration. The operator reported that a freshly built seed from the
same tip failed identically. If reproduced with a pinned binary and committed fixture, "registered in
`runtime_symbols.rs` but reported unknown at run time" would be the sharpest clue in this record;
the retained report alone does not eliminate binary provenance as a cause.

Also worth recording as a dead end: the failing `--keep-artifacts` run was checked for
`.sspec_wrapped_entry_*.spl`, but that is not the path produced by this code. At the original report
base, `build_coverage_wrapper` writes
`$TMPDIR/simple_cov_<flattened-source-path>_spec.spl`
(`test_executor_parsing.spl:804`), and every relevant cleanup branch is guarded by
`not options.keep_artifacts` (`test_runner_execute.spl:249-324,830-832`). The earlier claim that the
error path could remove the wrapper despite `--keep-artifacts` was false. The recorded directory
check looked for the wrong filename, so it proves neither creation nor non-creation. A repeat must
record the resolved temp directory and inspect the exact `simple_cov_...` path.

## REFRAMED (2026-08-27): investigate the directory/file symbol-registration difference

Two experiments were reported from a clean `origin/main` worktree with a two-file scratch repro:

**1. The duplicate-`discover_test_files` hypothesis is reported REFUTED.** There really are two
co-compiled definitions with different signatures —
`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl:410` `(base_path: text, options: TestOptions)`
and `src/app/test_daemon/daemon.spl:515` `(filter: text)`. Renaming the daemon's copy to
`daemon_discover_test_files` (so the collision is gone) changes nothing: the directory target still
aborts with the identical error. That observation removes the duplication from the active
investigation path; the missing patch and transcript prevent treating non-causation as sealed proof.

**2. MC/DC mode changes the first reported unresolved symbol.** Here, `unset` describes process
entry, not the mode used later: the runner resolves it to `on` and exports that value. Forcing the
effective mode to `off` with waiver atoms was reported to make the directory target fail on a
*different* symbol:

| `SIMPLE_MCDC_MODE` | abort |
|---|---|
| unset (resolves to `on`) | `variable mcdc_dynamic_probe_controller_load_builtin_current_owner not found` |
| `off` + waivers | `unknown extern function: rt_process_run_owned_observed_bounded_value` |

The original report says these used the same directory, binary, and specs, but it retained neither
the binary digest nor the exact four non-empty `SIMPLE_MCDC_OFF_WAIVER_*` values. The reported
mode-dependent change establishes no more than a lead: the MC/DC-on path reports the MC/DC symbol
first, while the reportedly waived-off path reaches an extern symbol. It neither rules MC/DC in or
out as a cause nor seals the second result without a replayable waiver command.

**What the recorded observations support:** the directory and file paths behave differently during
symbol resolution. The `unknown extern function` result makes module/extern registration the next
family to test (see `unregistered_extern_silent_nil_2026-08-01.md` and
`check-interpreter-extern-registry-gap.shs`); it does not by itself prove an extern-registration
root cause.

**Single next investigation:** commit a minimal two-file fixture, record the exact tested commit and
binary digest, then trace/diff module and extern registration for the directory command versus the
equivalent file command. Preserve stdout, stderr, exit status, resolved temp directory, and any
waiver values in an evidence bundle. Do not spend another iteration changing MC/DC or duplicate
definitions unless that trace shows they alter registration. Renaming this record once the mechanism
is known would be reasonable — its current name points at the symptom.

## Reported discriminator (2026-08-27): directory target aborts, file target does not

The report recorded this command pair:

```
bin/simple test test/zz_mini            --no-cover-check   ->  error: ... not found   (ABORTS)
bin/simple test test/zz_mini/foo_spec.spl --no-cover-check ->  Results: 1 total       (RUNS)
```

The report says `test/zz_mini` contained two ordinary compiler specs with no MC/DC reference. That
scratch directory, its second filename, and both file contents were not committed, so the exact
fixture cannot be reconstructed from `5c88fb433fa`. Treat the directory/file distinction as the
best recorded discriminator, not yet as a sealed reproduction.

If reproduced, that would narrow the search to what the directory path does differently from the
file path before the per-file loop — discovery/expansion and the session setup that follows it. It
would also explain the one fact that previously did not fit: a concurrent session's run was
executing specs normally because of how it invoked the runner, not because the defect was
intermittent.

## Earlier invalid `--no-mcdc` experiment and stale conclusion

An earlier draft of this record claimed that adding `--no-mcdc` avoided the abort, and concluded
MC/DC must be active by some non-env route. **That was wrong.** `--no-mcdc` is not a `test`
option at all — the run rejected it instantly with `Error: unknown option: --no-mcdc` and never
started, which was misread as "it got further". (`--no-mcdc` exists in
`src/compiler/00.common/config.spl:200`, the *compiler* CLI, not the test runner.)

The same draft then concluded there was no evidence of MC/DC involvement beyond the symbol name.
That conclusion is also **historical and false**: the runner resolves the unset/default mode to
`on`, and the operator reported a different first unresolved symbol after a waived `off`. Those
facts show mode-dependent execution, not whether MC/DC is a root cause. The invalid flag episode is
retained only to prevent its reuse as evidence.

## Operator-reported scope: multiple multi-file runs; provenance remains unverified

The report indicates this was not full-suite-specific:
`bin/simple test test/01_unit/compiler --no-cover-check` (2253 files, reportedly **zero** of which
reference MC/DC) aborted after `Session setup` before a per-file PASS/FAIL line. In the recorded
cases, the corresponding single-spec invocation reached a verdict and one cited spec passed 3/3,
including with `SIMPLE_MCDC_MODE=on --keep-artifacts`; this does not establish that every multi-file
run aborts or every single-spec run succeeds.

**Reported pre-redeploy reproduction; not provenance proof.** The operator reported stripping
`@always_inline` from 81 files and seeing the same missing-variable abort with a binary named
`simple.pre-alwaysinline-20260826`. The modified tree, command transcript, and binary digest were
not retained, so this observation does not prove independence from the redeploy or establish when
the defect was introduced.

The operator also reported a concurrent `test/01_unit` run, started at 00:36 on what was described
as the old pre-redeploy binary, executing specs normally with zero occurrences of this error. No
digest or transcript verifies that provenance. That run and these reportedly differed in tree
(shared versus clean worktree) and invocation, so the comparison is a lead, not corroboration or an
explanation.

## Additional facts

- **At the recorded code revision, MC/DC resolves on when the mode enters unset.**
  `test_runner_config.spl:249` calls
  `env_set("SIMPLE_MCDC_MODE", effective_mcdc_mode)` from `resolve_mcdc_mode_for_profile(...)`,
  so the two `mcdc_enabled` computations that read that variable see it set by the runner itself.
  This is why the earlier "MC/DC is not enabled here" reasoning was wrong.
- **Reported import-spelling probe.** The prelude's
  `use std.nogc_sync_mut.mcdc.dynamic_probe.{…}` is the odd one out among its siblings, which use
  short forms. The operator reported that rewriting it to `use std.mcdc.dynamic_probe.{…}` changed
  nothing and produced the same abort.
- **The wrapper check used the wrong path.** With `--keep-artifacts`, the run was checked for
  `.sspec_wrapped_entry_*.spl` under the target directory. The relevant code writes a
  `simple_cov_...` wrapper under the resolved temp directory and does not clean it when
  `keep_artifacts` is true. No execution-stage conclusion follows from the recorded check.
- The per-file loop begins immediately after the `Session setup: Nms` line
  (`src/app/test_runner_new/test_runner_main.spl:392-409`), so the failure is on the first file.

## Impact

In the recorded no-flag and directory-scoped runs, `bin/simple test` did not produce a tree verdict.
That evidence does not justify claims about every invocation or explain sessions that did execute
specs. No replayable workaround was retained: `--no-mcdc` is not a valid `test` option, and the
reported directory-scoped attempts also aborted. A working workaround or alternate entry point has
not been established.

(The `--no-cover-check` half is separate and benign — a documented preflight gate fires because
2113 system tests lack `# @cover`, and it announces itself and its bypass properly.)
