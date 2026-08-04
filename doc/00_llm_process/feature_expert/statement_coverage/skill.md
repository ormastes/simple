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

## Known Constraints / Verification

- Measured effect: dom.spl 28% -> 87% (80/91), dom_identity_index 40% -> 83%.
- Negative controls that must hold for any future attribution change:
  injected non-imported file attributes 0/108 (no over-attribution);
  called-gated modules stay byte-identical; a run WITHOUT SIMPLE_COVERAGE is
  byte-clean; the exercising spec stays green on every run.
- A file with zero recordable functions has no per-file evidence anchor —
  its method-only coverage cannot attribute; that is the current residual,
  not a bug in the caller's spec.

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
