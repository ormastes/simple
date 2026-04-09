---
paths:
  - "test/**"
  - "**/*spec*"
  - "**/*test*"
alwaysApply: false
---
# Testing Rules

- **NEVER skip/ignore** failing tests without user approval
- **Built-in matchers only:** `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
- Use `to_equal(true)` not `to_be_true()`
- **Interpreter mode limitation:** Test runner only verifies file loading, NOT `it` block execution
- **Live API tests:** `test/system/llm_caret_live_comprehensive_spec.spl` requires `CLAUDECODE=` env var (~$1-2 per run)

## Commands
```bash
bin/simple test                     # All tests
bin/simple test path/to/spec.spl   # Single file
bin/simple test --list              # List tests
bin/simple test --only-slow         # Slow tests
scripts/local-container-test.shs unit                     # Container tests
scripts/local-container-test.shs quick path/to/spec.spl  # Single container test
```

## SSpec Template
See `.claude/templates/sspec_template.spl`
