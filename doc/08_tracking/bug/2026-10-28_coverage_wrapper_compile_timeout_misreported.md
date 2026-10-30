# Coverage wrapper native-build timeout was reported as a compiler error

## Summary

When `simple test --coverage` compiles its generated instrumentation wrapper,
the test runner treated every nonzero compiler exit as a wrapper compile error.
A timeout therefore appeared as `coverage instrumentation wrapper failed to
compile`, with a partial source listing presented as its compiler diagnostic.
The result also set `timed_out: false` even though the scoped child reported a
wall timeout.

The run remained fail-closed: it did not execute the original uninstrumented
spec or claim coverage. The defect was the inaccurate failure class and missing
process evidence.

## Evidence

The bounded probe used the diagnostic TestRunner artifact
`d40d6133a414a6fdbc8d937b9f427794d83a75bd6cc445be0b29ffbbc5effd86` from
source head `0fa83a2e89ba73178336144efc63104e77cf6cc4`. Its pinned Phase1 child
was `aa58a24e…`, SHA-256
`ddd5aa4b9c47433ac814983d7499002a115e9f0e28f4623bfe26dba7e6b0a714`.

The coverage path ran:

```text
native-build --backend llvm --refresh-source-authority --entry-closure
  --entry <generated test/native-generated…/entry.spl>
  --runtime-bundle core-c-bootstrap --output <temporary coverage-native> --verbose
```

The runner printed that the checkout had no SCV compile-event journal and
enabled the one-time inventory cold-init path. With a 90-second per-test
timeout, it returned after 90,039 ms at 5,064,336 KiB peak RSS (about 4.8 GiB).
With a 300-second
timeout and an 8 GiB outer RSS cap, the child was still CPU-bound after almost
five minutes at 5,164,896 KiB peak RSS (about 4.9 GiB); the runner returned at
300,035 ms. In both runs the only surfaced “diagnostic” was the partial line
`98 | ) -> Result[(), PackageImageErrorV1]:`. It was not a compiler error: the
native build had been terminated by the requested timeout before it completed.
The generated coverage report contained only the schema headers and tracked no
files, so this probe produced no coverage percentage.

The earlier 12-second run also ended at its explicit timeout (12,018 ms). A
separate retry stopped at the explicitly enforced 4 GiB RSS cap, peaking at
4,349,408 KiB; that was a resource-cap stop, not a compile error.

The probe used the default machine-shared native-build cache. Setting
`SIMPLE_NATIVE_INCREMENTAL=1` would not help this path: that name is consumed
by bootstrap shell scripts, not the native-build compiler. No SCV journal was
reused or changed.

## Fix

The coverage abort now distinguishes the exact `limit_type == "timeout"`
case from ordinary compiler failures. Timeout results report the elapsed
compile time and partial compiler output, set `timed_out: true`, and retain
the Large compile resource class, resource usage, budget status, and process
completion receipt. Memory and other non-timeout failures stay in the compiler
failure class. All cases still fail closed before the spec executes and retain
the explicit uninstrumented fallback opt-in text.

## Regression evidence

On the original source, the focused regression spec was red: 6/9 passed and
three cases failed because the new failure-classification helper did not
exist. With the fix, the pinned Phase1 interpreter ran the spec with 9/9
passing. The tests cover timeout classification, real compiler errors,
memory-limit termination, resource metadata, and the fail-closed verdict.
This validates the failure-classification helper; it is not an end-to-end
successful instrumented coverage run. No instrumented coverage percentage was
measured, and this change does not claim that the underlying coverage build
completed.
