# `cargo test --lib -p simple-compiler` does not compile on aarch64 at `origin/main`
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN (2026-09-13)
- Found: 2026-09-13, PERF-9, running the mandatory before/after seed test leg
  after rebasing onto `origin/main` `6ff00b3df42`.
- Component: `src/compiler_rust/compiler/src/codegen/llvm/backend_core.rs`,
  the `#[cfg(test)]` block at :2009-2019.
- Landed by: `180c7a5cc88` "perf(codegen): let LLVM emit AVX-512 — the native
  default was pinned to AVX2" (PR #842).

## Symptom

```
error: This macro cannot be used on the current target.
       You can prevent it from being used in other architectures by
       guarding it behind a cfg(any(target_arch = "x86", target_arch = "x86_64")).
    --> compiler/src/codegen/llvm/backend_core.rs:2014:20  (and :2015, :2016)
error: could not compile `simple-compiler` (lib test) due to 3 previous errors
```

`cargo build --release --bin simple` is **unaffected** — the three uses are in
test-only code — which is why it reached `main`. Every aarch64 lane that runs
the seed's own unit tests is blocked.

## Cause

The test writes

```rust
let expected_wide = cfg!(target_arch = "x86_64")
    && std::is_x86_feature_detected!("avx512f") ...
```

`cfg!` is a RUNTIME boolean; it does not stop the macro being expanded, and
`is_x86_feature_detected!` refuses to expand off x86. The production code a few
hundred lines above (:152-164) gets this right with a real
`#[cfg(target_arch = "x86_64")] { ... }` block.

## Fix

Mirror the production guard — `#[cfg(target_arch = "x86_64")] let expected_wide
= std::is_x86_feature_detected!(...) && ...;` with a
`#[cfg(not(target_arch = "x86_64"))] let expected_wide = false;` companion.
Verified locally: with that change both `origin/main` and this lane's branch
compile and run the suite (4063 and 4065 passed, 19 failed, failure sets
identical).

**Not committed on this lane.** It is PR #842's defect, not PERF-9's, and PERF-9
applied it only as a disclosed, identical measurement patch to BOTH sides so the
before/after comparison could run at all. It needs an owner.

