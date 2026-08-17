# Instrumented statement-coverage tooling is inert (three independent breaks)

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).

**Date:** 2026-08-02 · **Severity:** medium · **Area:** test tooling / coverage
**Found during:** web-rendering GPU offload coverage campaign (goal: verify
≥90% on `src/lib/gc_async_mut/gpu/browser_engine/*` target modules).

## Symptom

There is currently **no working way to produce measured statement coverage**
for `.spl` modules. All three documented/likely entry points fail
independently:

1. `SIMPLE_COVERAGE=1 bin/simple test <spec>` — accepted, but **inert**: no
   coverage section in output, no coverage artifact written anywhere under
   `build/` or `doc/10_metrics/`.
2. `spl-coverage` — binary/subcommand is **not routed** from the deployed
   `bin/simple` dispatcher (no such subcommand; no standalone binary in
   `bin/`).
3. `bin/simple compile --coverage <file>` — rejected before compilation by the
   lint gate (**lint-blocked**), so an instrumented artifact can never be
   produced this way.

`bin/simple doc-coverage` works but measures **documentation** coverage, not
statement coverage — it is not a substitute.

## Impact

- Coverage targets declared via `@cover src/path.spl NN%` annotations in spec
  headers (the repo convention, first 30 lines of a spec) are **assertions
  without a measurement backend** — nothing verifies them.
- The web-rendering GPU offload campaign's "≥90% coverage" acceptance
  criterion can only be evidenced indirectly (spec breadth per module +
  per-case enumeration), not measured. See
  `doc/03_plan/platform/structural_compute/webrender_gpu_offload_plan.md`
  (Test evidence section) for the honest-caveat wording used.

## Expected

At least one of the three paths produces per-module statement (or line)
coverage for interpreter-mode spec runs, and `@cover` annotations are checked
against it (warn or fail on shortfall).

## Notes

- Any fix should live in pure Simple (self-hosted binary), per bootstrap
  policy; the seed runner path additionally never reaches `.spl` spec-libs
  (spec DSL is Rust intrinsics — see
  `doc/08_tracking/bug/` sspec notes and memory refs), so coverage
  instrumentation must hook the engine that actually executes `it` bodies
  (tree-walk interpreter under `bin/simple test`).

## GPU branch-coverage follow-up (2026-08-02)

The current dirty test-runner lane can emit heuristic per-file statement rows
when the daemon is bypassed, but it still emits no source decision inventory or
branch numerator/denominator. Focused Vulkan, CUDA, and Metal tests therefore
must retain `branch_coverage_percent=unavailable`; statement percentages and
scenario counts cannot satisfy the GPU backend NFR-008 threshold. Completion
requires compiler-owned decision-site enumeration plus true/false outcome
attribution to the original source file, including never-executed decisions.

## Update 2026-08-02 (later): under-attribution root-caused and fixed

Instance methods never reach the seed's `record_function_call`
(`interpreter_call/core/function_exec.rs` records free functions and
`static fn` only), so the attribution's `called.contains_key(fn)` gate
structurally vetoed every hit inside a method body — dom.spl read 1-28%
despite a 38/38 exercising spec. Fix in `test_runner_single.spl`: headers
classified recordable (column-0 `fn`/`gen`, `static`) vs instance method;
recordable keep the exact called gate, method bodies attribute on line-hit
plus per-file evidence (>=1 recordable function of the same file in the
called set). Measured: dom.spl 28% -> 87%, dom_identity_index 40% -> 83%,
non-imported control 0/108, previously-gated modules byte-identical,
no-env-var output byte-clean.
