# Statement Coverage Feature Expert

## Role

Own feature-specific process knowledge for **SIMPLE_COVERAGE statement
coverage** in the test runner: how line hits are attributed to source files,
the recordable-vs-instance-method gate, known collector limits, and the
verification evidence required for any attribution change.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Feature Links

- Source: `src/app/test_runner_new/test_runner_single.spl` (attribution gate
  lives here; run with `SIMPLE_COVERAGE=1 bin/simple test <spec>`).
- Collector limit (seed side): the seed interpreter records calls only for
  free functions and `static fn` (`function_exec.rs`) — instance-method names
  NEVER appear in the dump's called set.
- Bug doc:
  [instrumented_statement_coverage_tooling_inert_2026-08-02.md](../../../08_tracking/bug/instrumented_statement_coverage_tooling_inert_2026-08-02.md)
- Landing commits: `1a6c1e362a5` (working `SIMPLE_COVERAGE=1` statement
  coverage, pure-`.spl` wiring) then `d905ebdb7aa` (instance-method
  attribution fix, below).
- Owning layer: [test_runner layer expert](../../layer_expert/test_runner/skill.md)
  — child-env setup, spec-header directives, coverage report entry points
  (`_cov_report_for_file:494`, `_cov_print_report:537`).
- Attribution caveat seen in the GPU-offload campaign: `dom.spl` measures ~1%
  despite a green 38/38 DOM lane exercising it heavily. Treat low coverage on a
  green lane as an attribution question before calling the lane vacuous. See
  [gpu_offload_check](../gpu_offload_check/skill.md).

## Attribution model (2026-08-02, `d905ebdb7aa`)

Before the fix, the attribution gate required the enclosing function to
appear in the dump's called set — but since the collector never records
instance methods, every hit line inside a method body was vetoed. Modules
that are mostly methods (dom.spl: 17 of 27 callables) read 1-28% under a
38/38 exercising spec.

`test_runner_single` now classifies each function header as
**collector-recordable vs instance method**:

- **Recordable** (free functions, `static fn`): keep the exact called-set
  gate — a hit line attributes only if its enclosing function is in the
  called set.
- **Instance-method bodies**: attribute on line-hit plus **per-file
  evidence** — at least one of the file's recordable functions must be in
  the called set. This still blocks line-number-conflated hits on
  never-imported files (a hit at line N of file A must not attribute to
  line N of an unrelated file B).

## Running a coverage pass — three flags, or it executes ZERO tests

```bash
SIMPLE_COVERAGE=1 bin/simple test <path> --no-cache --no-cover-check --timeout 1800
```

- **`--no-cache` AND `--no-cover-check` are both required.** With either
  missing, an observed run emitted ~900 lines of lint, **exited 0, and executed
  zero tests** — cached results plus the coverage precondition check satisfy the
  invocation without running anything. `--no-cover-check` is parsed at
  `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:458` and announces
  itself as `Bypass: --no-cover-check` (`test_runner_main.spl:166`); the absence
  of that line in a log means the bypass was not applied.
- **`--timeout 1800`.** Without it the default budget expires and the timeout is
  reported as a spurious `1 failed` — a fabricated defect. Note the light daemon
  clamps `--timeout` at 600s
  ([test_runner layer expert](../../layer_expert/test_runner/skill.md)); a pass
  whose real cost exceeds that must be run detached and read from its log.
- **Score the verdict line, not the exit code.** Coverage runs are exactly the
  shape where exit-0-with-nothing-run is invisible: confirm a non-zero
  `Results: N total, ...` (or `SPEC FILE VERDICT ... executed=N`) before
  believing any percentage the run printed.

## Known Constraints / Verification

- Measured effect: dom.spl 28% -> 87% (80/91), dom_identity_index 40% -> 83%.
- Negative controls that must hold for any future attribution change:
  injected non-imported file attributes 0/108 (no over-attribution);
  called-gated modules stay byte-identical; a run WITHOUT SIMPLE_COVERAGE is
  byte-clean; the exercising spec stays green on every run.
- A file with zero recordable functions has no per-file evidence anchor —
  its method-only coverage cannot attribute; that is the current residual,
  not a bug in the caller's spec.

## U1.3 Prerequisite 5: rollup (2026-08-07)

- **New module:** `src/lib/common/coverage_sdn.spl` — parses SDN `lines` /
  `functions` / `sffi_calls` / `decisions` sections, merges by key (real
  set-union: shared `(file, line)` sums, disjoint keys stay separate), and
  re-renders with a freshly-computed `summary:` (never trusts a stored one).
  Spec + sabotage: `test/01_unit/common/coverage_sdn_spec.spl` (6 examples;
  sabotaging the merge to overwrite-instead-of-sum flips 2 to RED with
  `expected 5, got 2`).
- **`spl-coverage rollup --file A --file B [--out path]`**
  (`src/app/spl_coverage/main.spl`) unions N persisted `.sdn` artifacts. Fails
  CLOSED (distinct message, exit 1) on: zero `--file`, any missing/unreadable/
  empty/malformed input — never silently drops a bad file and prints a
  partial union.
- **Overwrite bug fixed:** `test_runner_single.spl`'s
  `SIMPLE_COVERAGE_OUTPUT` write previously OVERWROTE on every spec in a
  multi-spec run (last spec wins, silently dropping every earlier spec's
  coverage — the file's own comment called this out as blocked on
  prerequisite 5). Now: if the path already holds a well-formed prior
  artifact, merge the new spec's SDN into it before writing.
- **Rust fix, narrowly scoped:** the interpreter's own SFFI shim for
  `rt_coverage_dump_sdn` (`interpreter_extern/coverage.rs`) previously
  returned ONLY the compiler-level line/function tracker
  (`crate::coverage::get_global_coverage()`), silently dropping the separate
  runtime decision/condition/path global
  (`runtime/src/coverage.rs::COVERAGE_DATA`) even when decisions WERE being
  recorded into it by the interpreter's own `record_decision_coverage_sffi`
  in the same process. Fixed to merge both, mirroring the existing
  `save_global_coverage()` export-path merge. In-process A/B proof: a
  top-level `if` recorded a real decision before the fix and after, but only
  after the fix did `coverage_dump_sdn()` (called from Simple) surface a
  `decisions` section for it.
- **Real, deeper, NOT fixed here — separate gap, needs its own fix:**
  `record_decision_coverage_sffi` is called only from
  `interpreter_control.rs`'s `exec_if` / `exec_while` / `exec_match_core`
  (used for TOP-LEVEL module statements via
  `interpreter/node_exec.rs::exec_node`). Branches INSIDE a called function's
  body or a BDD `it` block execute through
  `interpreter_call/block_execution.rs`'s own separate `Node::If` handling
  (lines ~434, ~1201), which never calls `record_decision_coverage_sffi` at
  all. Measured: a top-level `if` under `SIMPLE_COVERAGE=1
  SIMPLE_EXECUTION_MODE=interpret` records a real decision; the same `if`
  moved inside a `fn` body records none. This means decision/branch rows
  reaching `spl-coverage dump` today are real only for top-level control
  flow, not for the common case (branches inside functions/specs) — file as
  a follow-up bug before trusting a per-file branch-coverage percentage.

## CLI end-to-end + gate now 5/5, real collector blind spots pinned (2026-08-07)

- **`spl-coverage --file` added to `dump`/`status`** (`70907278997`,
  `9c5bcf07449`): cross-process artifact inspection no longer needs the
  in-process global — pass a persisted `.sdn` path directly. Fixed alongside a
  real import-path bug (`spl-coverage` imported nonexistent `app.io.mod`
  symbols; dispatch was broken before this landed).
- **`scripts/check/check-render2d-coverage.shs` now PASSes all 5 prereqs**
  (`2effdbde400`, superseding the prior perma-`UNVERIFIED_BY_SCRIPT` rows for
  prereqs 1/2): prereqs 1/2 compile a tiny branching probe via
  `bin/simple compile --emit-mir=<path>` with `SIMPLE_COVERAGE` unset vs `=1`
  and inspect the MIR JSON directly for a `DecisionProbe` instruction with a
  real (non-`<source>`, non-`<entry>`, non-0/0) `file`/`line` — isolating
  production MIR lowering from both the interpreter and the test-runner path
  (an earlier draft comparing `bin/simple test --coverage` runs was
  inconclusive: both gave `total_decisions=57`). Prereq 3 now sets
  `SIMPLE_COVERAGE=1` before probing `spl-coverage status` (exit 1 on
  *disabled* coverage is documented behavior, not a dispatch failure — testing
  it unset conflated the two). Prereq 5 rolls up two independent runs of the
  same spec and checks a decision id's `true_count` sums correctly (picked
  nonzero-in-both so `0+0=0` can't read as a false MET) and the merged row
  keeps per-file identity. **Caveat: this PASS depends on uncommitted Rust
  seed source** (`interpreter_extern/coverage.rs`, `runtime/src/coverage.rs`)
  not yet landed on `origin/main` as of this session — re-verify the gate
  after that Rust work lands, don't cite PASS as durable until then.
- **Known collector gaps, confirmed real (not yet fixed):** function
  **signature lines and tail-expression lines are invisible** to the line
  collector (only statement-body lines register a hit); **`elif`/`else`
  header lines** don't register independently of their branch body;
  `<entry>`-attributed hits (the seed's synthetic top-level-module
  pseudo-function) don't map back to a real file/line; and **line sparsity in
  large function bodies** — a function with many statements can show a hit
  ratio well under 100% even when every logical branch executed, because only
  a subset of statement-shaped lines are individually instrumented. Treat a
  per-file percentage as a floor, not the true statement count, until these
  are addressed.
- **`spl-coverage rollup`'s `summary:` block is recomputed, not copied** —
  `coverage_sdn.spl:227-257` iterates the merged rows fresh on every rollup.
  But "recomputed" does not mean "meaningful" for both axes: it is
  **tautological in practice for LINE coverage**, because coverage artifacts
  only ever contain rows for lines that were actually executed, so
  `covered_lines == total_lines` always holds at this stage regardless of
  how partial the underlying runs were; it is **genuinely discriminating for
  DECISION coverage**, since a decision row only counts as covered when both
  `true_count>0` and `false_count>0`, which a partial run can and does leave
  unmet. Verify this before trusting a rollup's line-coverage summary as
  "coverage achieved" rather than "coverage observed across the inputs
  given" — the decision-coverage summary does not have this caveat.

## 2026-08-08: impl-block methods stopped landing on `<entry>` (`b6a43042`)

`Node::Impl` handling in `interpreter_module`'s `register_definitions()`
never called `tag_methods_owner`/`tag_function_module_owner` on impl-block
methods (unlike `Node::Class`/`Struct`/`Enum`, which all tag their inline
methods). `function_module_owner()` returned `None` for every impl-block
method body, so `CURRENT_EXEC_MODULE` stayed unset while they ran and
`current_coverage_file()` fell back to the `<entry>` sentinel. This is the
confirmed root cause of the previously-reported "line coverage tops out at
143" sparsity for `engine2d_baremetal_core.spl` — those rows were never
missing, they were correctly-numbered lines misfiled under `<entry>` because
`draw_rect_stroked`/`draw_circle_stroked`/`draw_image`/`draw_codes12_block`
are impl-block methods. A/B probe: `engine2d_baremetal_core.spl` coverage
6% (13/209) -> 62% (131/209); `<entry>` rows in the impl block's line range
(240-389) 73 -> 0; max real-path line 143 -> 389 (file's last line).

**Still open — RC2:** entry-script top-level functions never get an owner
registered at all (a second, distinct root cause, not fixed this pass). See
`doc/08_tracking/bug/coverage_entry_placeholder_two_root_causes_2026-08-08.md`.
The rollup-tautology, signature/tail-expr/elif-line blindness, and 90%
line-target-unreachable caveats above are unaffected by this fix and remain
open.

## Update Rule

When the project process creates or changes research, requirements,
architecture, design, tests, implementation, verification, or release
artifacts for this feature, update this skill with the new links and the
current handoff notes.

## Update Checklist

- Add links to new or changed requirements, architecture, design, plans,
  specs, and reports.
- Record affected layers and link their layer expert skills.
- Record implementation constraints, known blockers, and required
  verification commands.
- Update this file after each pipeline stage before handing off to the next
  stage.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
