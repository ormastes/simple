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

## 2026-11-26 aarch64 run (lane work/bug-arm64-tooling-20261126, base `c07c1b8248d`)

Host aarch64 Linux (GB10). `cargo test -j6 --workspace --lib --no-fail-fast`
from `src/compiler_rust`, own `CARGO_TARGET_DIR`, `MemoryMax=24G`.

**Compile blocker: gone.** `cargo test --workspace --lib --no-run` exits 0;
every lib test binary of the workspace builds and runs on aarch64.

Baseline (gates as in tree): 8263 passed / 59 failed.
- simple-runtime 34 failures are all parallel interference (shared `GUARD`
  poison cascade, process-global registries): `--test-threads=1` gives
  **1594 passed / 0 failed**.
- Isolated re-runs (`--exact`, one thread) of the 25 non-runtime failures:
  10 pass alone; 15 still fail deterministically; arch not established (no
  x86 `cargo test` log was retrievable for comparison; no arch reference seen
  in the inspected tests or paths): `mir::reachability` x2, `pipeline::native_project` x7
  (incl. the 4 recorded 2026-11-05 and a link-time `rt_value_eq` undefined),
  `extern_drift_tests` (stale allowlist `rt_enum_new`), `collection_capture`,
  `module_loader` (nogc_sync_mut io package), `value_tests_basic`
  `shared_text_unicode_index_and_slice` (byte vs char slice semantics),
  driver `build_cache` override hash, runtime_abi `realloc` manifest order.

**Un-gated on aarch64 (x86-only gate not needed: no inline asm, Cranelift has
an arm64 ISA):** `codegen::jit` tests (`jit.rs`), `codegen::local_execution_tests`
(`codegen/mod.rs`), `cranelift_sffi` `stack_probe_tests` (cross-target AOT
only) and `tests` (now x86_64|aarch64, JIT calls use a host-ISA
`JIT_HOST_TARGET`; previously hard-coded `CL_TARGET_X86_64`, which
`build_jit_isa_and_triple` correctly refuses off x86), `repl_runner_sffi`
tests, and `driver/tests/runner_tests.rs`.
Two stale runner_tests expectations fixed (target-independent logic, hidden because CI
never ran this target on aarch64 and `rust-tests.yml` excludes simple-driver):
file-backed SMF now embeds an `.interp_snapshot` instead of refusing
(contract in `pipeline::execution` tests), and 32-bit `arm-linux` without the
`llvm` feature is refused earlier with "32-bit targets require the LLVM
backend".

After: 8381 passed / 34 failed (simple-compiler 5160/18 with 72 more tests
executed than before; runner_tests **51/51 pass**). Only newly-enabled test
still red: `codegen::local_execution_tests::test_cranelift_jit_typed_dict_float_literal_key_compatibility`
— deterministic in isolation: `map.get(1.0)` returns a TAG_HEAP pointer
instead of 7 and `has/contains(1.0)` returns false; filed separately as
`jit_dict_f64_key_get_membership_aarch64_2026-11-26`. Left red, not re-gated.

Parallel-only note: `cranelift_sffi::abort_tests` (documented "run serially")
reset the whole provider registry, so with the extra un-gated cranelift tests
the simple-compiler-backfill binary fails 2-3 abort tests per parallel run
(0 with `--test-threads=1`, 32/32). One intermediate run, before the
`JIT_HOST_TARGET` fix, SIGSEGVed that binary; the final run did not.
`extern_drift_tests` asks to drop `rt_enum_new` from its allowlist; not
applied here (outside this lane).

Still x86-gated and untouched: `driver/tests/{synthetic_driver_registration_live,
anti_dummy_quality_cli_tests,os_cli_dispatch_tests,help_output_tests}.rs`
(x86_64) and `native_compile_size_reporting.rs` (x86_64+linux).
