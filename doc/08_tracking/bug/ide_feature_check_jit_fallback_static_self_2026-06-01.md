# IDE feature check JIT fallback on static self lowering

## Closed 2026-09-13 — Does not reproduce: no static-`self` JIT fallback in the feature-check run

- **measured** `bin/simple-interp src/app/ide/main.spl --feature-check --tui` -> `EXIT=0`; `grep -c 'JIT compilation failed' <log>` returns `0`, so the reported `HIR lowering error: cannot use self in static method` fallback line is absent.
- **measured** Host binary is the Windows Rust seed `v1.0.0-rc.1`, the same interpreter/JIT driver family the entry was filed against.
- **inferred** Only `--tui` was exercised; both modes share the import closure and lowering path, so the offending receiver form is gone from that closure.


Status: closed (2026-09-13 triage) — see the "Closed 2026-09-13" section below

## Status
closed (2026-09-13 triage)

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
