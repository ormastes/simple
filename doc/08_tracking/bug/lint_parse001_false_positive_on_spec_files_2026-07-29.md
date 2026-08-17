# lint PARSE001 false positive on `use std.spec.*` describe-specs (2026-07-29)

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Status Update (2026-07-30)

**Item 1 (PARSE001 false positive): FIXED** by commit f4adc39bf39 (2026-07-28).
The fix introduced `parse_module_silent_checked()` which returns the parse-error
state by value, avoiding module-boundary flag loss. Verified: valid specs now
pass lint (0 PARSE001 errors), invalid specs are correctly rejected with PARSE001.

---

Found during lane L5 (stage4 memory gate spec). Three related lint/tooling
defects, items 2-3 remain report-only:

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
