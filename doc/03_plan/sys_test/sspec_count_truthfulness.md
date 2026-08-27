# SSpec Count Truthfulness System-Test Plan

**Current execution status: TEST_BLOCKED** — no admitted current-source
pure-Simple CLI was available while this plan was authored. Static design and
manual review are possible now; runtime, SPipe, `sspec-maintain`, and docgen
must wait for a qualified environment.

## Scope

This plan verifies `scripts/check/check-sspec-count-truthful.shs` as an
operator-visible infrastructure boundary. It covers runner identity admission
(REQ-SCT-001), preservation of nonzero runner results (REQ-SCT-002), and exact
anchored declared/reported count agreement (REQ-SCT-003).

The executable target is:

`test/03_system/infra/sspec_count_truthfulness_spec.spl`

Its authored documentation mirror is:

`doc/06_spec/03_system/infra/sspec_count_truthfulness_spec.md`

## Exclusions

- SSpec language-parser conformance beyond the gate's anchored `it` pattern.
- Performance, parallel execution, network behavior, and platform portability.
- Rust-seed, stale-binary, mocked-admission, or manually rewritten evidence.
- Changes to the SSpec runner, SPipe implementation, or shared global skills.
- Any claim that authored Markdown is generated or executable evidence.

## Environment and admission

Run only from a clean isolated checkout of the source revision under test.
Set `SIMPLE_BIN` to a pure-Simple self-hosted CLI built from that revision and
first require the canonical self-hosted identity/admission check to succeed.
Use the tracked non-discovered lane fixtures and preserve the process exit
status and output for each scenario.

If no CLI satisfies admission, record **TEST_BLOCKED** and stop. A Rust seed,
an older deployed CLI, or an environment override that bypasses identity may
not execute or generate evidence for this lane.

## Execution design

The future executable spec contains four independent scenarios:

1. A two-example passing fixture yields status `0`, `OK`, and exact
   `declared=2 reported=2` evidence.
2. An anchored-count fixture adds comment/string/identifier lookalikes around
   one real example while retaining status `0` and exact count one.
3. A deliberately failing fixture yields nonzero status, a runner-exit
   diagnostic, and no `OK` verdict.
4. An explicit missing `SIMPLE_BIN` yields status `2`, `SKIPPED (cannot test)`
   and `This is NOT a pass` diagnostics, and no `OK` verdict.

Assertions use built-in SSpec matchers only, including `to_equal`,
`to_contain`, `to_start_with`, and numeric `to_be_greater_than`. Every
scenario includes concrete status and output assertions; no scenario may use
`pass_todo`, unconditional truth, empty bodies, or silent placeholder helpers.

## Pass and fail rules

**PASS** requires one qualified run in which all four executable scenarios
pass, static quality and repository guards pass, `sspec-maintain` reports no
maintenance defect, docgen reports the affected spec complete with `0 stubs`,
and the generated/manual review retains the claim boundary and every frozen
visible step.

**FAIL** applies when an admitted run produces any count mismatch, false-green
exit, missing verdict, inflated anchored count, swallowed runner failure,
placeholder assertion, stub, omitted frozen step, or nonzero required guard.

**TEST_BLOCKED** applies when the only unavailable prerequisite is an admitted
current-source pure-Simple CLI. It must not be collapsed into PASS or FAIL and
must retain the qualification diagnostic.

## Manual visibility contract

The executable spec and its manual must preserve these exact visible steps:

1. `Select the admitted pure-Simple SSpec runner`
2. `Run the count-truthfulness gate on a two-example passing spec`
3. `Confirm declared and reported counts agree`
4. `Run the count-truthfulness gate on the anchored-count edge fixture`
5. `Confirm non-example text does not inflate the declared count`
6. `Run the count-truthfulness gate on a deliberately failing spec`
7. `Confirm the runner failure remains nonzero`
8. `Run the count-truthfulness gate with a missing compiler path`
9. `Confirm unavailable identity is TEST_BLOCKED and never PASS`

Setup and cleanup details may be folded. Outcome steps and their associated
exit/output evidence may not be hidden.

## Evidence capture

Retain the following together:

- source commit, worktree, executable-spec hash, and gate-script hash;
- admitted CLI path and canonical identity/admission transcript;
- exact commands, per-command exit statuses, and captured output;
- SSpec result summary with scenario count;
- `sspec-maintain` result;
- docgen completion and `0 stubs` result;
- generated/manual diff or review result for the nine frozen steps; and
- static-quality and repository-guard results required by the lane.

Do not accept screenshots without machine-readable status or a hand-edited
summary without the raw command provenance.

## Exact future commands

Run these only after `/absolute/path/to/admitted/simple` has passed canonical
self-hosted admission for the checked-out source. Replace the placeholder with
that admitted path; do not point it at the Rust seed.

```sh
SIMPLE_BIN=/absolute/path/to/admitted/simple \
  /absolute/path/to/admitted/simple test \
  test/03_system/infra/sspec_count_truthfulness_spec.spl --clean

SIMPLE_BIN=/absolute/path/to/admitted/simple \
  /absolute/path/to/admitted/simple sspec-maintain scan \
  test/03_system/infra/sspec_count_truthfulness_spec.spl

SIMPLE_BIN=/absolute/path/to/admitted/simple \
  /absolute/path/to/admitted/simple spipe-docgen \
  test/03_system/infra/sspec_count_truthfulness_spec.spl \
  --output doc/06_spec --no-index
```

After docgen, require its affected-spec result to say complete with `0 stubs`,
then compare the output to the authored mirror. If the installed admitted CLI
uses a different accepted argument order, confirm it through that CLI's own
help and record the exact qualified command; do not trial commands through an
unadmitted binary.

## Risks and controls

| Risk | Control |
|---|---|
| False green from prefix execution | Assert exact declared/reported equality and exit status |
| Regex counts lookalike text | Dedicated anchored edge fixture with exact count one |
| Runner failure is swallowed | Deliberate red fixture; require nonzero gate status and diagnostic |
| Missing compiler reads as skip/pass | Explicit missing-path scenario; require nonzero and TEST_BLOCKED wording |
| Unqualified runtime contaminates evidence | Canonical admission precondition; no seed or stale fallback |
| Manual drifts from executable flow | Freeze nine exact steps and compare after zero-stub docgen |
| Fixture state leaks between scenarios | Use immutable tracked fixtures with no generated state |

## REQ-to-scenario matrix

| Requirement | Positive | Edge | Error/qualification |
|---|---|---|---|
| REQ-SCT-001 | Qualified self-hosted identity precedes green path | Edge path also records admitted identity | Red path records admitted identity; missing binary exits `2` and is TEST_BLOCKED |
| REQ-SCT-002 | Green path preserves exit `0` | Edge path preserves exit `0` | Failing child preserves exit `1`; missing identity preserves exit `2` |
| REQ-SCT-003 | Two-example exact equality | One real example plus lookalikes still reports one | Runner failure cannot become an `OK` count claim |
