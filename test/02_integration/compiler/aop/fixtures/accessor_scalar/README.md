# Scalar accessor native qualification fixture

Status: authored, **not run**. Current public get/set validation must reject this fixture with E1507. Do not count that rejection as a successful woven-program test, weaken the validator globally, or substitute handwritten getter/setter wrappers for compiler generation.

When the actual source-site consumers are connected, compile this exact source through the admitted self-hosted compiler, with a recorded no-GC synchronous provider and optimized native profile. The logical module must be `main`. Retain compiler/source/provider/cache identity, emitted MIR/object evidence and process exit/output.

Required exit is 0 and stdout is exactly:

```text
7
before-read
after-read
rhs
receiver
before-write
after-write-committed
```

The getter must return its single pre-advice scalar load even though after-success advice allocates and mutates the same object through an unselected setter. The setter must evaluate RHS before receiver, evaluate each once, store through the original reference and run success advice after the store. Advice allocation/churn must use the real provider; no substituted callbacks.

Also run a distinct active-transient-scope scenario: create the receiver in the owner scope, run the same synchronous workload without retiring that scope, then retire it after the last valid use. Verify ownership validity before/after with the provider's non-dereferencing validity API. Never execute an invalid post-scope dereference. This second scenario is not implemented in `main.spl` yet; it remains a qualification requirement.

This fixture does not establish helper single-definition/private linkage, no-aspect identity, exception/failure behavior, moving collectors, managed field values, generics, value structs or compound places. Those gates remain separate and open.
