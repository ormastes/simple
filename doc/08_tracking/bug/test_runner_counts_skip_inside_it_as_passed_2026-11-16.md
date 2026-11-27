# Test runner counts `skip()` inside an `it` as passed (skipped=0)

Symptom: an example whose body calls `skip(name, reason)` is reported as a pass: the log shows a green
check for it, `SPEC FILE VERDICT ... passed=N skipped=0`, and `Results: N total, N passed, 0 failed`.
A spec whose environment gate is unmet therefore reports success without testing anything.

Minimal repro (2026-11-16, Rust seed `bin/simple.exe test`, Windows):

    use std.spec.{describe, it, expect, skip}
    describe "runner repro":
        it "skips inside an it":
            skip("skips inside an it", "reason")
        it "passes":
            expect(1).to_equal(1)

Result: `executed=2 passed=2 failed=0 skipped=0`, `Results: 2 total, 2 passed, 0 failed`.
Expected: `skipped=1`, passed=1.

Observed in: slang live specs (`test/03_system/lib/slang/feature/slang_pure_kv_cache_spec.spl` was vacuous on
this host because of a separate `env_get(..) ?? default` bug, and still counted as passed). Workaround in the
slang specs: every skip also appends `SKIPPED: <why>` to a file under `build/probe/`.
Not fixed here.
