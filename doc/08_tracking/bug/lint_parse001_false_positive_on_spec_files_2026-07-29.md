# lint PARSE001 false positive on `use std.spec.*` describe-specs (2026-07-29)

Found during lane L5 (stage4 memory gate spec). Three related lint/tooling
defects, all report-only so far:

1. **PARSE001 false positive:** `bin/simple lint` reports
   `error[PARSE001]: Source did not parse` on ANY describe-spec importing
   `use std.spec.*` — including committed green specs (reproduced on
   `aetheric_host_web_gui_evidence_spec.spl` and a 7-line trivial spec). The
   seed parses these files and the interpreter runs them green, so lint's
   parse front-end diverges from the real parser. Same family as
   `reference_lint_does_not_catch_syntax_errors` (verification layer
   fail-open — here it's fail-CLOSED on valid input, equally trust-eroding).
2. **SPIPE005 ignores `assert_true`/`assert_equal`:** the "no real assertion"
   recognizer (`src/compiler/90.tools/lint/_LintMain/traceability_and_assertions.spl`
   ~line 382) does not count the standalone assertion helpers that
   `.claude/rules/testing.md` explicitly recommends. Workaround: direct
   `expect()` matchers.
3. **`@step "..."` template syntax doesn't parse:** the annotation form in
   `.claude/templates/spipe_template.spl` fails with `expected Fn, found
   FString`; live convention is `# @step:` comments + in-body `step("...")`.
   Template needs updating or the grammar needs the annotation form.

Repro for (1): `bin/simple lint test/03_system/check/stage4_memory_gate_spec.spl`
(errors) vs `SIMPLE_EXECUTION_MODE=interpreter bin/simple test <same file>`
(Results: 2 total, 2 passed).
