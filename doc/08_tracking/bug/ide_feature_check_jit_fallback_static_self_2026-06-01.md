# IDE feature check JIT fallback on static self lowering

Status: Open -> CLOSED-STALE (2026-09-12: re-verification attempt timed out; not re-verifiable from the record)

## Status
Open

## Observed
Running either IDE feature-check mode exits `0` and prints the expected capability
report, but the runtime falls back from JIT to interpreter first:

```text
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: cannot use `self` in static method
```

Commands:

```bash
timeout 30s bin/simple-interp src/app/ide/main.spl --feature-check --tui
timeout 30s bin/simple-interp src/app/ide/main.spl --feature-check --gui
```

## Impact
The IDE sanity checks prove interpreter behavior but do not prove the warm JIT
path for the feature-check import closure. This is relevant to IDE startup and
feature-check latency.

## Notes
The scoped Office app receiver cleanup removed local `fn ... self` usage from the
Office app modules imported by the IDE feature checks, and deprecated generic
indexing warnings were removed from the direct output. The fallback remains,
which suggests an older receiver form still exists deeper in the imported
editor/UI/runtime closure or the lowerer is misclassifying a valid receiver.

## Follow-up
- Identify the exact module/function reported by HIR lowering.
- Convert the offending receiver form or fix the lowerer diagnostic.
- Add a focused regression check that fails when IDE feature checks fall back
  from JIT to interpreter.

## Triage 2026-09-12
Re-verification attempted 2026-09-12: `bin/simple-interp src/app/ide/main.spl --feature-check --tui` did not complete within 40s (Terminated), so the original JIT-fallback claim could not be confirmed or refuted. Older than 45 days; closing per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
