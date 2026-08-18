---
paths:
  - "test/**"
  - "**/*spec*"
  - "**/*test*"
alwaysApply: false
---
# Testing Rules

- **NEVER skip/ignore** failing tests without user approval
- **A correct spec that fails is a legitimate artifact.** When a spec rightly
  asserts behaviour the implementation does not yet have, leave it RED, file a
  `doc/08_tracking/bug/` record with file:line and the unblock condition, and
  report it as a genuine failure. Never weaken the assertion, mark it pending,
  or rewrite it until it passes — a known-failing spec documents a real defect;
  a quietly-softened one hides it.
- **Every bug fix ships two specs** (2026-08-17): one reproducing the exact
  defect, plus a generalization spec probing similar problems nearby (same
  pattern, adjacent code paths). Cite both in the `doc/08_tracking/bug/` record.
  A fix without its reproducing spec is not done.
- **NEVER disable** sdoctest (md-embedded) or spl_doctest (comment-embedded) — both must stay on
- **Test database sequential access** (F2): Section/directory test runs must be SEQUENTIAL — parallel `simple test path/to/dir` invocations corrupt the shared test database. Use single-spec targets or wrap in a serial runner. See `doc/07_guide/infra/testing.md` § "Runner Operational Caveats".
- **Results line is authoritative** (F3): Only the final `Results: N total, ...` summary line is authoritative test verdict. Compile diagnostics quote runner source with "passed"/"failed" tokens — grepping those misleads. Always inspect the bottom-line result summary. See `doc/07_guide/infra/testing.md` § "Runner Operational Caveats".
- **Built-in matchers:** `to_equal`, `to_be`, `to_be_nil`, `to_be_truthy`, `to_be_falsy`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`. NOTE: `to_be_true`/`to_be_false` are REJECTED by the runner on bool receivers (two lanes verified 2026-07-05) — use `assert_true`/`assert_false` or `to_equal(true)`.
- **Standalone assertions:** `assert_true`, `assert_false`, `assert_equal`, `assert_not_equal`, `assert_contains`, `assert_nil` -- use these for bare boolean/equality checks instead of `expect(x).to_equal(true)`
- **`bin/simple test` DOES execute `it` bodies** (verified 2026-07-28): a deliberately-wrong oracle fails with `expected 0 to equal 999`, exit 1, and several specs went red that night on real assertion failures. The older note claiming the runner "only verifies file loading" is stale for this path. What *is* still true: running a spec file through `SIMPLE_EXECUTION_MODE=interpreter bin/simple run <spec>` can emit only lint warnings and never reach execution.
- **`run` and `test` are DIFFERENT ENGINES** (2026-07-28): `bin/simple run` uses the Cranelift JIT; `bin/simple test` hard-defaults to the tree-walk interpreter, and `TestExecutionMode` has no JIT variant — so the spec suite **cannot** reach the engine ordinary programs run on. 18 of 49 measurable builtins disagree between them, the interpreter being correct in all 18 (`arr.first()` → 80 instead of 10 on the JIT; `filter`/`any`/`all` SIGSEGV; `text.to_upper` a silent no-op). **711 of 23,958 spec files call at least one divergent method** and would stay green through any JIT regression. Full table: `doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`.
- **`SIMPLE_NO_JIT=1` is a DECOY** — no reader anywhere in `src/compiler_rust/`; it is read only by the pure-Simple interpreter. Any A/B done with it proves nothing. The working knob is `SIMPLE_EXECUTION_MODE=interpreter|jit`.
- **One unsupported operation silently demotes the WHOLE program to the interpreter** — a single `d.insert(...)` is enough, and demotion also triggers on source *text* (`std.cli`, `get_cli_args`, `window_winit`). A 44-line combined probe reported 38/38 AGREE for exactly this reason. Keep each probe in its own minimal file.
- **Take `$?` from the command under test, never from a pipe.** `bin/simple` prints thousands of lines of lint noise *before* results, so `| grep … | head` both truncates the summary and replaces the exit code with `head`'s. That combination turned "8 examples, 4 failures, exit 1" into a reported "zero examples, exit 0". Capture to a file and read the tail.
- **Match `examples\?`, not `examples`** — the plural-only pattern silently drops a `1 example, 0 failures` block and makes a later run look like it grew a describe block.
- **Binary identity caveat:** Test evidence is only as good as the binary that produced it. Before trusting test results, verify which binary ran: `bin/simple --version` checks for a seed warning banner; `readlink -f bin/simple` shows whether you're on a stale bootstrap seed. A seed + old mtime means findings apply to SEED, not self-hosted — attribute accordingly. Known mode: `simple test` on a stale seed hangs (see `deployed_seed_test_runner_init_hang_2026-07-17.md`).
- **Live API tests:** `test/03_system/llm_caret_live_comprehensive_spec.spl` requires `CLAUDECODE=` env var (~$1-2 per run)

## Modern SSpec

Write specs manual-first so `spipe-docgen` generates a scenario manual, not a
test log: user-voice `"""..."""` docstrings, outcome-named `it` blocks,
imperative `step("...")` calls (or `@step`-named helpers), capture evidence
(tui_grid, gui_image, protocol_json/binary, bit_table, statistics, or
user-registered kinds), `@manual_section` groupings, and `# @req REQ-*`
traceability comments (parsed via grep convention until FR-6 lands native
parsing). See glossary: [SSpec (Modern SSpec)](../../doc/glossary.md),
anti-patterns: `doc/07_guide/infra/sspec_antipatterns.md`, example manuals:
`doc/07_guide/app/spipe/scenario_manual_example.md` +
`doc/07_guide/app/spipe/manual_examples/`, requirements:
`doc/02_requirements/feature/sspec_scenario_manual.md`.

### Typed evidence oracles

An observation (screenshot, terminal grid, protocol transcript, bytes, scene graph) is
**not an oracle** — it proves something was captured, not that it was correct. Typed
evidence declares checks as data and evaluates them fail-closed.

- Modules: `src/lib/common/spec/evidence/model.spl` (records, selectors, `oracle_spec`),
  `src/lib/common/spec/evidence/evidence_comparator.spl` (fail-closed evaluation + manual
  projection).
- Fail-closed rules: parse error, unresolved selector, ambiguous cardinality, ignore
  without a reason, all-ignore vacuity, closed-mode undeclared field, zero positive
  resolutions — each fails the capture rather than reporting a clean pass.
- `check_full_pattern` patterns are **anchored class tokens** (`hex:16`, `digit:*`,
  `alnum:N`) — never regex, never substring match.
- Run with `bin/simple run <spec>`, not `test`: the `test` daemon path trips the
  800-module transitive-import cap during load.
- Guide: `doc/07_guide/infra/sspec_typed_evidence.md`. Glossary:
  [Typed Evidence](../../doc/glossary.md).

### Scoring & modernization triage — `sspec-maintain scan`
Score a spec/dir for modernness: `simple sspec-maintain scan <spec|dir>` (7
weighted dimensions → `SSpec documentization score: N/100`). Operator manual:
`doc/07_guide/infra/sspec_documentization_maintenance.md`.

- **Deployed-binary gotcha (2026-08-08):** `bin/release/<triple>/simple` is
  currently the Rust **seed**, whose CLI lacks `sspec-maintain` (it prints the
  seed banner and falls through to "file not found"). Verify with
  `bin/simple --version` (seed warning) / `readlink -f bin/simple`. Until the
  self-hosted binary is rebuilt (`scripts/setup/setup.shs && bin/simple build
  bootstrap` then redeploy), run the scorer **from source** — one stdlib load
  scans a whole tree in ~90s:
  `bin/simple src/app/sspec_maintain/main.spl scan <path> 2>/dev/null`.
- **Rank by `raw=`, not the headline score.** Any blocker clamps the effective
  score to 49 (`score.spl`), so across a legacy tree nearly every spec reads
  `49/100` and the headline can't rank them. Parse the `raw=` line instead
  (lower = more findings) and triage by blocker type.
- **Modernization signals, strongest first:** `blocker SSDOC-ORA-001`
  (unconditional pending / fail-fast scaffold — the spec asserts nothing real;
  the `core/core_integration_N`, `e2e/*_integration_N`, `lib/database_*`,
  `io/native_ops_*` families are synthetic filler) → `SSDOC-ORA-003`
  (unexplained numeric expected values) → `SSDOC-NAR-001` (no authored
  purpose/audience) → `SSDOC-TRC-001` (no `# @req REQ-*` traceability). Fix
  ORA-001 first: replace the scaffold with a real oracle or delete the spec.

## Measurement traps (all three observed 2026-08-10)

These produced wrong verdicts in a single review session. They are cheap to avoid
and expensive to miss.

- **Never A/B across two trees.** An agent measured "before" in the main checkout
  and "after" in its worktree and reported a **12.4× speedup**; the controlled A/B
  in one tree with one binary gave **13%**. The shared checkout carries a large
  pile of uncommitted files and different cache state. Toggle ONLY the change under
  test, hold the tree and binary fixed, and state which produced each number.
- **A pipe launders the exit code.** `sh guard.shs | tail -1; echo $?` reports
  `tail`'s status — this read a correctly fail-closed gate (exit 2) as exit 0,
  i.e. "the guard fails open" when it did not. Capture first:
  `out=$(sh guard.shs); rc=$?`.
- **A scan that finds nothing may have scanned nothing.** A `sorry`/`admit` grep
  came back clean against a path that did not exist. Pair every absence check with
  a control that MUST produce a hit; if the control is silent, the scan is broken,
  not the code.

Related, already documented elsewhere but same family: a silently-failed `git
fetch` makes a comparison run against an empty object and report a false
divergence; `simple test <ABSOLUTE path>` runs nothing and exits 0.

## Commands
```bash
bin/simple test                     # All tests
bin/simple test path/to/spec.spl   # Single file
bin/simple test --list              # List tests
bin/simple test --only-slow         # Slow tests
scripts/local-container-test.shs unit                     # Container tests
scripts/local-container-test.shs quick path/to/spec.spl  # Single container test
```

## SPipe Template
See `.claude/templates/spipe_template.spl`

## Silent green: exit 0 is not a pass (2026-08-17, HIGH)

`bin/simple test <spec>` has been measured printing ~1897 lines — all warnings
— with **zero** pass/fail/scenario/total lines, and exiting **0**. A spec that
never ran is then indistinguishable from a spec that passed, on the command
every session uses as evidence. Bug (OPEN):
`doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md`.

Rule: **never accept exit 0 as proof of pass.** Require an explicit
results/count line in the captured output. If there is none, the result is
**INCONCLUSIVE** — not green — and must be confirmed by a direct
`bin/simple run` repro of the behaviour under test before any claim is made.
Same family as the already-listed `simple test <ABSOLUTE path>` no-op.

## Detectors (guards, censuses, scans) — standard

Anything that REPORTS defects follows `doc/07_guide/infra/detector/detector_standard.md`.
Minimum before a detector is BLOCKING rather than advisory:
- fatal `--selftest` with must-FAIL fixtures, not just must-PASS;
- non-vacuity (`n > 0` or `ERROR — nothing was checked`, exit 2);
- three-way PASS/SKIP/FAIL so "can't tell" is never a pass;
- explicit recorded escapes (`--expect-files`/`--expect-removals` style), never silent thresholds;
- a STATED, MEASURED false-positive rate on a named hand-adjudicated sample (N>=15),
  as a `# FP-RATE: k/N (pct%) on <sample>, measured <date>` header line.
Any number whose hits were not all adjudicated is an **UPPER BOUND**, and must be
labelled that way in the verdict, doc, and commit message — never as a defect COUNT.
