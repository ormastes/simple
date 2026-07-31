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
`use std.spec.*`, imperative `step("...")` calls, direct value assertions,
capture evidence (text, still, motion, inert HTML, or raw-plus-decoded
protocol fields), `@manual_section` groupings, and `# @req REQ-*`
traceability comments (parsed via grep convention until FR-6 lands native
parsing). See glossary: [SSpec (Modern SSpec)](../../doc/glossary.md),
anti-patterns: `doc/07_guide/infra/sspec_antipatterns.md`, example manuals:
`doc/07_guide/app/spipe/scenario_manual_example.md` +
`doc/07_guide/app/spipe/manual_examples/`, requirements:
`doc/02_requirements/feature/sspec_scenario_manual.md`.
Critical features link their generated operator manual from
`EVIDENCE_SHOWCASE.md`; validated manifests, not prose, own status and
artifacts. Never place executable specs under `doc/06_spec/`.

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
