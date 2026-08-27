# lint JSON fix output was mixed and dry-run was inert

**Status:** SOURCE FIXED / PURE-SIMPLE DEPLOY VERIFICATION PENDING
**Severity:** P1 — structured output and advertised dry-run were incorrect

## Reproduction

- `simple lint <spec> --json --fix` mixed human `Applied ...` text into JSON
  Lines output.
- `simple lint <spec> --fix-dry-run` did not collect fixes unless `--fix` or
  `--fix-all` was also present.
- fix-write failure was ignored after a delete-first write.

## Solution

All three fix modes enter fix collection. JSON mode emits only structured
diagnostic, file-summary, fix-summary, and error records. Fix writes use the
canonical atomic owner and propagate failure. The public CLI contract launches
the same pure-Simple executable that runs the spec, bounds every child to 30
seconds, uses PID-unique fixtures, parses every JSON line, proves dry-run does
not mutate, and verifies the exact applied source.

JSON escaping now covers backspace, form-feed, and all remaining control bytes.
Its parser-backed unit regression is included.

## Evidence

- interpreter atomic provider regression: PASS
- native-all atomic regression: authored; bounded execution cap already reached
- pure-Simple JSON/fix CLI contract: pending an admitted Stage 4 executable
