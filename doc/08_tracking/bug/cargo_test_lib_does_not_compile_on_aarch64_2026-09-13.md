# `cargo test --lib -p simple-compiler` does not compile on aarch64 at `origin/main`
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: SUPERSEDED (2026-09-13)
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


## Verification evidence — 2026-11-05 (aarch64 host, worktree `work/libbug-linux-cargotest-20261105` @ `origin/release/1.0.0` `adfeae3765c`)

Host: aarch64 Linux. `cargo 1.99.1 (5f94df478 2026-08-27)`, `rustc 1.99.1 (58cf8f9c3 2026-10-13)`.

Command (from `src/compiler_rust/`, worktree-local `target/`):

```
cargo test --lib -p simple-compiler
```

Result: **the target package now COMPILES on aarch64** — the
`is_x86_feature_detected!` macro-expansion blocker is gone. On
`origin/release/1.0.0` the test at issue is `common/src/target.rs:1304-1320`
`the_host_target_widens_exactly_when_the_host_admits_avx512`, now behind a real
`#[cfg(target_arch = "x86_64")]` (matching the fix sketched above); production
probe `common/src/target.rs:303-312` is likewise cfg-guarded, and
`compiler/src/codegen/llvm/backend_core.rs` `default_x86_64_cpu_tests` no longer
references the macro.

Suite executed: `test result: FAILED. 4608 passed; 8 failed; 5 ignored; 0 measured; 0 filtered out; finished in 224.51s`

The 8 failures are unrelated to this bug (no macro-expansion/compile errors;
all are runtime assertion failures):

- `interpreter::interpreter_extern::vulkan::tests::{family_size_is_pinned,
  text_return_is_text_not_int, text_returning_entry_points_are_typed_as_text}`
  — registry/runtime skew: `VULKAN_FNS.len()` is 132 vs pinned 131, and
  `rt_vulkan_get_last_error` is in the registry but not linked into the test
  binary (expected 7 text returns, got 8). Cross-component drift, needs owner.
- `mir::lower::tests::branch_coverage::calls::primitive_field_method_call_is_builtin_qualified`
  — expects a `MirInst::MethodCallStatic` with `func_name == "i32.to_string"`;
  lowering emits something else.
- `pipeline::native_project::tests::{test_bootstrap_mutex_capsule_exports_only_canonical_bootstrap_abi,
  test_core_lane_runtime_required_abi_stdout_stderr_and_values,
  test_runtime_bundle_hosted_is_allowed_for_bootstrap_entry_only,
  test_simple_core_source_tree_emits_partial_runtime_archive}`
  — native-build probe mismatches (extra `rt_secure_temp_dir_*`/`rt_process_rss_kib`
  exports, exit codes 44/77 from ABI probes, hosted archive path expectation).

No fix attempted on this lane: none of the 8 is the aarch64 compile blocker
this bug tracks, and the vulkan pin/count skew is a deliberate anti-inflation
guard that needs the owning lane's context. Diagnosed first failure verbatim:
`family_size_is_pinned`: `assertion left == right failed: left: 132, right: 131`
at `compiler/src/interpreter_extern/vulkan.rs:487`.

## 2026-11-10 status — SUPERSEDED (P3 library lane, work/p3-lib-20261110)

Confirmed the 2026-11-05 verification evidence still holds on
origin/release/1.0.0: the aarch64 compile blocker is fixed in-tree.
`common/src/target.rs:1303` guards
`the_host_target_widens_exactly_when_the_host_admits_avx512` behind a real
`#[cfg(target_arch = "x86_64")]` (the `cfg!` + `is_x86_feature_detected!`
anti-pattern is gone), the production probe at `common/src/target.rs:304-308`
is likewise cfg-guarded, and
`compiler/src/codegen/llvm/backend_core.rs` no longer references
`is_x86_feature_detected!`. This lane is not the src/compiler_rust owner; no
change made here.

## 2026-11-11 status — SUPERSEDED (P3-essential library lane, work/p3-lib3-20261111)

Confirmed again on this lane's base (`790b54f7c4fc`): the fix is intact
and attributable to PR #7597 (merge `9e7e7a526edb`) — real
`#[cfg(target_arch = "x86_64")]` guards at `common/src/target.rs:304` and
`:1303`, and zero `is_x86_feature_detected!` references in
`backend_core.rs` (grepped). Host-limit unchanged: no aarch64 host/cargo
in this lane, so the executed leg remains the 2026-11-05 aarch64 run
recorded above (target package compiles; 4608 passed / 8 failures all
unrelated to this bug). No evidence to the contrary.
