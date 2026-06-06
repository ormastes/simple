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
- **Built-in matchers:** `to_equal`, `to_be`, `to_be_nil`, `to_be_true`, `to_be_false`, `to_be_truthy`, `to_be_falsy`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
- **Standalone assertions:** `assert_true`, `assert_false`, `assert_equal`, `assert_not_equal`, `assert_contains`, `assert_nil` -- use these for bare boolean/equality checks instead of `expect(x).to_equal(true)`
- **Interpreter mode limitation:** Test runner only verifies file loading, NOT `it` block execution
- **Live API tests:** `test/03_system/llm_caret_live_comprehensive_spec.spl` requires `CLAUDECODE=` env var (~$1-2 per run)

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
