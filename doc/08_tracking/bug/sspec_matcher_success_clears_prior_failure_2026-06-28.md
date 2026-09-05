# SSpec matcher success cleared prior failure

Status: fixed in source, pending deployment to the default `bin/simple`

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
