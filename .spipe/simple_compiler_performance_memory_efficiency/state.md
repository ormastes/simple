# Feature: Simple Compiler Performance and Memory Efficiency

## Raw Request

Deepen `simple_compiler_performance_memory_efficiency_audit.md`, create the
architecture and execution plans with parallel review, harden compiler and lint
warning/error behavior in pure Simple, and remove evidenced performance and
memory-efficiency defects from Simple and its tools.

## Task Type

code-quality

## Refined Goal

Make Simple's optimizer and performance diagnostics truthful, conservative,
shared, and measurably efficient while preserving language behavior and public
interfaces.

## Acceptance Criteria

- AC-1: The current repository has one reviewed research audit that separates
  observed code, derived risk, measured impact, and unmeasured hypotheses, and
  reconciles the August 22 snapshot with current HEAD.
- AC-2: Architecture and detail design define the four analysis tiers, shared
  typed `PerfFacts`, honest pass status/expectation contracts, structured
  diagnostics/remarks, conservative alias/effect/escape authority, bounded
  analysis, cache invalidation, and failure-closed behavior.
- AC-3: The system-test plan and agent-task plan map every requirement to owned
  evidence, identify parallel review lanes, merge owner, final reviewer, shared
  interfaces, and any intentionally deferred work.
- AC-4: At least one current, reproduced compiler or lint hot-path defect is
  fixed in its pure-Simple owner without changing public behavior; the exact
  reproducer and one adjacent/root-cause regression are retained.
- AC-5: Every touched hot path is reviewed in order for algorithmic complexity,
  allocations/copies, data layout/locality, loop hoisting, and dispatch cost.
- AC-6: Optimizer transformations touched by this lane fail closed unless their
  legality and semantic contracts are proved; registered skeleton/analysis-only
  passes are not represented as active transformations.
- AC-7: Warning/error changes preserve diagnostic code, severity, ordering,
  evidence, uncertainty, fixes, text output, and JSON behavior unless a final
  requirement explicitly changes one of them.
- AC-8: One relevant baseline and the identical post-change measurement record
  elapsed time plus peak RSS or allocation evidence where meaningful; remaining
  compiler/runtime blockers become concrete tracked bugs rather than unsupported
  performance claims.
- AC-9: Risky optimizer or diagnostic behavior has real Simple/SPipe correctness
  coverage, with no placeholder assertions, and each acceptance check is run at
  most once after the final edit.
- AC-10: Knowledge is updated in `doc/01_research`, `doc/04_architecture`,
  `doc/05_design`, `doc/03_plan`, and the applicable `doc/07_guide`; feature and
  compiler/lint layer expert `skill.md` files are updated or explicitly marked
  N/A with reasons; every unresolved gap has a `doc/08_tracking/bug` record with
  file/line evidence and an unblock condition.
- AC-11: Workflow/tooling surfaces affected by the implementation keep mirrored
  `doc/06_spec` manuals and relevant Codex/Claude/Gemini instructions current,
  or each unaffected surface is explicitly N/A; executable specs remain outside
  `doc/06_spec`.
- AC-12: The owned diff contains no unrelated concurrent work, retains a linear
  reviewable history, and its final report distinguishes verified results from
  static review and deferred evidence.

## Scope Exclusions

- No blanket activation of dormant optimizer implementations.
- No C or Rust replacement for a pure-Simple compiler/tool hot path.
- No automatic source-level data-structure or loop rewrite where ordering,
  effects, aliasing, lifetime, or profitability is unresolved.
- No release/version bump unless separately requested after verification PASS.

## Cooperative Review

- Sidecars: `pass_integrity_review`, `lint_perf_review`, and `docs_plan_review`.
- Merge owner: root Codex agent in this worktree.
- Final reviewer: root Codex agent at the highest available capability.
- Shared interfaces: `PassStatus`, `PassExpectation`, `PerfFactRequest`,
  `PerfFacts`, `PerfSummary`, `OperationSummary`, `OptimizationRemark`, and
  stable diagnostic records.
- Manual flow helpers: `step("inspect optimizer truth")`,
  `step("collect typed performance facts")`,
  `step("report or transform conservatively")`, and
  `step("compare bounded evidence")`.
- Setup/checker helpers: `setup_perf_fixture`, `check_pass_contract`,
  `check_diagnostic_parity`, and `check_perf_budget`.
- Any scaffold introduced before its oracle exists must use `fail(...)` or
  `assert(false)` and cannot satisfy an acceptance criterion.
- Generated-manual review owner: root Codex agent.

## Phase

dev-done

## Log

- dev: Created state file with 12 acceptance criteria (type: code-quality).
