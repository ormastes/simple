---
paths:
  - "test/**"
  - "**/*spec*"
  - "**/*test*"
alwaysApply: false
---
# Testing Rules

- **NEVER skip/ignore** failing tests without user approval
- **NEVER disable** sdoctest (md-embedded) or spl_doctest (comment-embedded) — both must stay on
- **Test database sequential access** (F2): Section/directory test runs must be SEQUENTIAL — parallel `simple test path/to/dir` invocations corrupt the shared test database. Use single-spec targets or wrap in a serial runner. See `doc/07_guide/infra/testing.md` § "Runner Operational Caveats".
- **Results line is authoritative** (F3): Only the final `Results: N total, ...` summary line is authoritative test verdict. Compile diagnostics quote runner source with "passed"/"failed" tokens — grepping those misleads. Always inspect the bottom-line result summary. See `doc/07_guide/infra/testing.md` § "Runner Operational Caveats".
- **Built-in matchers:** `to_equal`, `to_be`, `to_be_nil`, `to_be_truthy`, `to_be_falsy`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`. NOTE: `to_be_true`/`to_be_false` are REJECTED by the runner on bool receivers (two lanes verified 2026-07-05) — use `assert_true`/`assert_false` or `to_equal(true)`.
- **Standalone assertions:** `assert_true`, `assert_false`, `assert_equal`, `assert_not_equal`, `assert_contains`, `assert_nil` -- use these for bare boolean/equality checks instead of `expect(x).to_equal(true)`
- **Interpreter mode limitation:** Test runner only verifies file loading, NOT `it` block execution
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
