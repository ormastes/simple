# Interpreter coverage: conditions never recorded, unvisited decisions omitted from the denominator

- **Date:** 2026-10-19
- **Status:** OPEN
- **Severity:** high for coverage gating — a 100% decision/condition gate on
  this data measures nothing for conditions and rewards *not* calling code.
- **Blocks:** lane C "crypto and compress default to dynload" Part 2
  (100% decision/condition gate on `src/lib/common/{crypto,compress}`).

## Binary identity

- Deployed `bin/simple` -> `bin/release/aarch64-unknown-linux-gnu/simple`,
  sha256 `44a07ae51c5dd308553cb06203e3e92d0a468b68ffaa28773af0fde0c7ac2c2d`,
  Rust seed `v1.0.0-beta.14` (2026-09-26). Cannot load the current tree at all:
  `parse: src/lib/nogc_sync_mut/io/windows_redirected_process.spl: Unexpected
  token: expected Fn, found Colon` (top-level `@when(os=...)`, seed parser fix
  `e1a0b17c8c6` landed 2026-10-09, after this binary).
- Probe seed: `phase2-six-results-20261011/current-release-producer/.../bootstrap/simple`,
  sha256 `423eb4b85dfe7012dd55e6a49424b736bcd9766bdea3f06e4108baecb44ea4ca`,
  `v1.0.0-rc.1` (2026-10-11).

## Defects (all with `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_COVERAGE=1`)

1. **`test --coverage` does not run a spec.** With the rc.1 seed:
   `error: spawned test process did not publish a valid child APK activation
   receipt`. The artifact is still written, but holds only 113 decisions from
   the test runner's own files (`test_runner_client.spl`, `process_governor.spl`,
   ...), none from the spec. Only `simple run <spec>` records the spec's files.
2. **Conditions are never instrumented.** `if n > 0 and m > 0:` exercised on
   (T,T), (F,T), (T,F) yields `total_conditions: 0`, `condition_percent: 100.0`
   — a vacuous 100%.
3. **Unvisited decisions are absent from the denominator.** A fixture with an
   uncalled function's `if`, an unreached `elif`, an `if`-expression, a `while`
   and a `match` reports `total_decisions: 3` (only the reached `if`, `while`,
   `match`); the uncalled `if`, the `elif` and the `if`-expression are missing.
   On real scope code, `test/01_unit/lib/crypto/chacha20_poly1305_spec.spl`
   records `common/crypto/poly1305.spl` 2/7 decisions while the file has 12
   `if`/`elif`/`while` sites; `chacha20_poly1305.spl` 15/18 recorded vs 18.

Decision *counts* that are recorded are correct (true/false split matched the
calls in every fixture).

## Reproduce

```sh
cat > build/cov_fixture_spec.spl <<'EOF'
fn classify(n: i64, m: i64) -> text:
    if n > 0 and m > 0:
        return "both"
    else:
        return "other"
describe "coverage fixture":
    it "takes both branches":
        expect(classify(1, 1)).to_equal("both")
        expect(classify(-1, 1)).to_equal("other")
EOF
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=/tmp/c.sdn \
  <seed> run build/cov_fixture_spec.spl
grep total_conditions /tmp/c.sdn   # total_conditions: 0
```

## Unblock condition

A gate may claim decision/condition percentages only after (a) condition
probes are emitted for `and`/`or` operands, (b) the denominator comes from a
static enumeration of every decision site in the file (visited or not), and
(c) `test --coverage` runs the spec in the child on a binary that can load the
current tree.
