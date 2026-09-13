# SSpec matcher success cleared prior failure

## Closed 2026-09-13 — fix is deployed; a passing matcher no longer clears an earlier failure

- **measured** Binary: Rust seed `bin/simple` v1.0.0-rc.1 (16,347,136 bytes, 2026-09-02), Windows host.
- **measured** Running the entry's own minimized repro (`expect("deliberate").to_equal("failure")` then `expect(1).to_equal(1)`) prints `spec failure: 1 of 1 example(s) failed (exit 1)` and `outcome=ERROR` — the old behaviour was `1 example, 0 failures`.
- **measured** No false-green in the other direction either: a spec whose only assertions pass reports `0 failures`.

Status: closed (fixed + deployed) 2026-09-13

## Summary

An SSpec example could execute a failing matcher and then report green if a
later matcher in the same `it` passed. The original symptom appeared in the GUI
RenderDoc aggregate autodiscovery spec and looked like a long-command or
tail-assertion problem, but the minimized repro is:

```simple
describe "fail then pass":
    it "keeps the first failure after later passing assertions":
        expect("deliberate").to_equal("failure")
        expect(1).to_equal(1)
```

Old behavior:

- `bin/simple run ...` printed `1 example, 0 failures`.

Root cause:

- `src/compiler_rust/compiler/src/interpreter_method/mod.rs` cleared
  `BDD_EXPECT_FAILED` and `BDD_FAILURE_MSG` when any matcher passed.
- The `it` block should reset assertion state only at example start. A passing
  matcher must not erase an earlier failure in the same example.

Fix:

- Matcher pass branches no longer clear `BDD_EXPECT_FAILED` or
  `BDD_FAILURE_MSG`.
- Regression test:
  `src/compiler_rust/driver/tests/interpreter_bdd.rs`.

Verification:

```sh
cd src/compiler_rust
cargo test -p simple-driver --test interpreter_bdd bdd_matcher_pass_after_failure_keeps_example_failed
```

Focused run passed on 2026-06-28. A rebuilt debug binary also reports the
minimized repro and the reduced GUI RenderDoc repro as failures.

Remaining:

- Deploy/rebuild the default `bin/simple` path before treating SSpec output from
  this host as release evidence.
