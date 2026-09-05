# Test runner: file-level `Failed` count includes a phantom +1 after all `it` examples pass

**Date:** 2026-07-20
**Component:** `bin/simple test` (SSpec runner), file-level result aggregation
**Severity:** High — makes `PASS`/`FAIL` and the `Passed:`/`Failed:` summary
unreliable for any spec that pulls in a large transitive-import graph; the
per-example results (`✓`/`✗` lines and the in-spec `N examples, M failures`
tally) are correct, but the outer `Test Summary` block adds an extra
`Failed: 1` that has no corresponding `✗` line or assertion-failure message
anywhere in the output.
**Found by:** whole-suite triage campaign, `test/02_integration/` cluster
(individual re-run pass, `timeout 90 --no-session-daemon` on
`bin/release/x86_64-unknown-linux-gnu/simple`)

## Symptom

Every `it`/`slow_it` example in the file prints `✓` and the spec's own
mid-file tally line (`N examples, 0 failures`) confirms zero failures, but
the trailing `Test Summary` block still reports `Failed: 1` (one more than
the real failure count, which is 0), and the file is marked `FAIL` with a
bare `error: test-runner: spec failed` — no assertion text, no exception
message, nothing attributable to a specific example.

Between the last `✓`/tally line and the `error: test-runner: spec failed`
line, the log always contains a large amount of unrelated compiler
diagnostic noise (deprecated-generics warnings, `self.` style-lint notes,
`[gc-warning] Higher-layer module ... imported in restricted context`) from
what looks like a much bigger transitive-import compile than the spec's own
`use` list would suggest — consistent with a late second pass over the
whole dependency graph (doctest scan of imported modules is the leading
hypothesis, since `testing.md` requires `sdoctest`/`spl_doctest` stay
enabled, but nothing in the log names which doctest ran or why it counted
as a failure).

## Confirmed instances (this triage pass)

| Spec | In-file tally | Outer summary |
|---|---|---|
| `test/02_integration/app/mcp_context_ponytail_dispatch_spec.spl` | `11 examples, 0 failures` | `Passed: 11, Failed: 1` |
| `test/02_integration/app/loader_run_function_spec.spl` | `1 example, 0 failures` | `Passed: 1, Failed: 1` |
| `test/02_integration/app/model3d/model3d_nested_nodes_spec.spl` | `3+2+3=8 examples, 0 failures` (per describe block) | `Passed: 8, Failed: 1` |
| `test/02_integration/app/restaurant_webapp_spec.spl` | `7+4+3+2=42 examples (aggregated), 0 failures` (per describe block) | `Passed: 42, Failed: 1` |
| `test/02_integration/app/scv_cli_dispatch_spec.spl` | `1 example, 0 failures` (single `✓`) | `Passed: 1, Failed: 1` |
| `test/feature/usage/arch_check_error_cases_spec.spl` | `6+6+10+5+5+2+4+5=43 examples (per describe block)` | `Passed: 43, Failed: 1` |
| `test/unit/app/dashboard_framework_policy_spec.spl` | `9 examples, 0 failures` | `Passed: 9, Failed: 1` |
| `test/unit/app/duplicate_check/detector_grouping_spec.spl` | `3 examples, 0 failures` | `Passed: 3, Failed: 1` (noise between the tally and the phantom failure includes a `Usage: simple_lint <file.spl> [options]` help-text dump — an apparent malformed `simple_lint` subprocess invocation triggered while loading `compiler.tools.duplicate_check.*`, consistent with the "late second pass over the whole dependency graph" hypothesis above) |
| `test/unit/compiler/linker/lib_smf_format_spec.spl` | `4 examples, 0 failures` | `Passed: 4, Failed: 1` |

All five (plus the `feature/usage` instance added by a later triage pass):
rerun individually via
`SIMPLE_RUST_SEED_WARNING=0 timeout 90/180 bin/release/x86_64-unknown-linux-gnu/simple test <spec> --no-session-daemon`
— reproduces deterministically, not a WALLED-sweep contention artifact (each
was re-verified with no other `simple test` process running concurrently).

## Related but distinct

`test/02_integration/app/loader_exec_memory_spec.spl` shows a similar-looking
`Passed: 0, Failed: 1` with `error: test-runner: no examples executed`, but
that one has a clear, different, non-mysterious cause: the whole `describe`
block is tagged `tag: ["only-compiled"]` and gated by a
`# skip: native exec memory functions require compiled mode (not
interpreter)` comment — every `it` is behind that tag filter, so 0 examples
ever run under a plain interpreter-mode `test` invocation. That is an ENV
limitation (needs compiled/native-build mode), not this phantom-failure
defect — left separate here on purpose so it isn't miscounted into either
bucket.

`doc/08_tracking/bug/sspec_runner_file_pass_with_example_failures_2026-06-27.md`
documents the **inverse** mismatch (file marked `PASS` despite real example
failures) and is dated as already addressed; this is a new, opposite-facing
divergence between the per-example ledger and the file-level verdict, so it
is filed separately rather than reopening that doc.

## Root-cause hypothesis

Not confirmed from source (out of triage scope — no Rust seed changes
attempted). Leading candidate: a post-example phase (most likely embedded
doctest scanning across the full transitive `use` graph, given the sheer
volume of unrelated-module compiler warnings that appear only in the failing
files) increments the file's failure counter without printing which check
failed or why. All five confirmed instances share the trait of importing
a large module graph (MCP dispatcher, loader/SFFI, model3d nested nodes,
restaurant webapp with DB/email/delivery submodules, SCV CLI registry).

## Recommended fix direction (not attempted here)

Either (a) attribute the phantom failure — print which doctest/late-check
failed and why, or (b) if it is spurious/redundant with the doctest run
already covered elsewhere, stop double-counting it into the file's
`Failed` tally. Whichever direction, the fix belongs in the test-runner
source (interpreter/tooling), not in these five spec files, which are
correct as written.
