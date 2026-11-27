---
id: cranelift_seed_missing_sffi_externs_2026-07-16
status: RESOLVED 2026-11-25 (missing-extern defect stale w.r.t. pinned seed; see dated note)
severity: medium
discovered: 2026-07-16
discovered_by: scripts/check/check-native-seed-parity.shs strict-cranelift family (all 9 cases red at tip de7cb5a238a)
related: src/compiler/70.backend/backend/cranelift_codegen_adapter.spl
related: src/lib/nogc_sync_mut/sffi/codegen.spl
related: src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs
related: scripts/check/check-native-seed-parity.shs
---

# Strict-cranelift native-build cannot run: deployed seed binary lacks 9 rt_cranelift_* SFFI externs

## Summary

`bin/simple native-build --backend=cranelift` interprets
`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl` live, which
calls the `rt_cranelift_*` SFFI surface declared in
`src/lib/nogc_sync_mut/sffi/codegen.spl` (74 externs). The deployed seed
binary (`bin/release/x86_64-unknown-linux-gnu/simple`) exports only 68 of
them. Missing:

- rt_cranelift_call_arg
- rt_cranelift_call_args_clear
- rt_cranelift_data_addr_in_func
- rt_cranelift_declare_global_data
- rt_cranelift_declare_string_data
- rt_cranelift_emit_object_raw
- rt_cranelift_fdemote
- rt_cranelift_fpromote
- rt_cranelift_function_addr_in_func

The first extern actually reached in even the most trivial program
(`fn main(): print("ok")`) is `rt_cranelift_declare_string_data`, so EVERY
cranelift build dies at interpretation time with:

```
error: semantic: unknown extern function: rt_cranelift_declare_string_data
```

All 9 `*_llvm_cranelift` cases in `check-native-seed-parity.shs` fail for
this ONE reason — none of them is a per-construct cranelift codegen bug.
These cases were added while native-build was broken and have never executed
green on the cranelift leg.

## Ground truth

- The Rust implementations DO exist in
  `src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs` (e.g.
  `rt_cranelift_declare_string_data` at line 517 and registered at line
  1684). The deployed seed simply predates them.
- Verified by `nm --defined-only` on the deployed binary vs
  `grep -o "rt_cranelift_[a-z_0-9]*" src/lib/nogc_sync_mut/sffi/codegen.spl`.

## Fix

Redeploy the seed / self-hosted binary from current source (bootstrap
rebuild), which exports the full cranelift SFFI surface. Until then the
parity harness records the strict-cranelift legs as XFAIL via a memoized
capability probe (`cranelift_seed_supported()` in
`scripts/check/check-native-seed-parity.shs`) that only downgrades on the
exact `unknown extern function: rt_cranelift_` signature; any other
cranelift failure still FAILs loudly. Once a capable seed is deployed the
probe passes and all 9 cases run for real (no code change needed).

## Related latent fix banked in the adapter

While diagnosing, a REAL pre-extern blocker was found and fixed in
`cranelift_codegen_adapter.spl`: `declare_module_statics` returned
`Dict<i64,i64>?`, and in the live-interpreted native-build context an
Option<Dict> return is erased to nil even when the callee returns `Some`
(see interp_option_dict_return_erased_2026-07-16.md), so the cranelift path
failed with "Failed to declare module statics" before ever reaching the
missing externs. The adapter now returns a plain Dict with a `-1` sentinel
failure key.

## Update 2026-07-17: earliest-failure point moved even earlier (10th missing extern)

Re-verified from a fresh `wt_clif` worktree at origin tip `5aee6bc6a25` (this
doc's binary evidence is unchanged: same deployed
`bin/release/x86_64-unknown-linux-gnu/simple`, built 2026-07-11 08:52, 68
`rt_cranelift_*` symbols, all 9 originally-listed names above still absent
per `nm --defined-only`).

Same-day commit `f26cccd64fb` ("fix(cranelift): preserve target triple for
AOT", 2026-07-16 17:10 UTC) changed `cranelift_new_aot_module` in
`src/lib/nogc_sync_mut/ffi/codegen.spl` and
`src/lib/nogc_sync_mut/sffi/codegen.spl` from calling the old
`rt_cranelift_new_aot_module(name_ptr, name_len, target: i64)` (int target
code, present in the deployed seed) to calling a brand-new
`rt_cranelift_new_aot_module_triple(name_ptr, name_len, target_ptr,
target_len)` (full target-triple text, for correct cross-compile AOT). This
extern is registered in `interpreter_extern/mod.rs` and implemented in
`codegen/cranelift_sffi.rs` in current HEAD source, but — like the 9 above —
the deployed seed binary predates it (`nm` count: 0).

Net effect: `rt_cranelift_new_aot_module_triple` is called **first**. inside
`cranelift_compile_module_direct`/`compile_module`, immediately after
resolving the target triple and before `declare_module_statics` or any
function/string declaration is reached. So the very first cranelift SFFI
call in the entire pipeline now fails, for every program without exception
— reproduced with the smallest possible probe:

```
fn main():
    print(42)
```

```
env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH bin/simple native-build \
  --entry probe1.spl -o probe1_bin --backend cranelift --clean
...
[cranelift-direct] start
[cranelift-direct] target
error: semantic: unknown extern function: rt_cranelift_new_aot_module_triple
```

This is strictly earlier than the previously-documented
`rt_cranelift_declare_string_data` failure point (module creation happens
before any static/string declaration), so the total missing-extern count is
now **10**, not 9. No pure-Simple logic bug: the call site is internally
consistent with the current Rust seed source; the gap is purely deployed-
binary staleness (same root cause, same fix — redeploy).

The `cranelift_seed_supported()` capability probe in
`scripts/check/check-native-seed-parity.shs` needs **no change**: its match
is the generic prefix `unknown extern function: rt_cranelift_` (not tied to
one symbol name), so it already downgrades this case to XFAIL correctly
regardless of which of the 10 missing externs is hit first.

Verdict for this pass: **BLOCKED-on-seed**, no code change applied. A
targeted pure-Simple revert (fall back to the old int-target-code extern for
the plain host-native case, only using the new triple extern when
`SIMPLE_NATIVE_BUILD_TARGET` requests real cross-compilation) was considered
and rejected: it would only relabel the failure from
`rt_cranelift_new_aot_module_triple` to the already-documented
`rt_cranelift_declare_string_data` (or similar) a few instructions later —
every cranelift build still XFAILs either way under this seed — so it is
pure churn against an already-correct call site for zero verification-gate
benefit. Fix remains: redeploy the seed/self-hosted binary from current
source.

## Verification 2026-11-25 (p2w1-ag lane, symbol inspection + bounded probe)

The missing-extern defect is STALE with respect to the currently pinned seed
(`bin/simple.exe`, Rust seed v1.0.0-rc.1, Windows, 38,403,072 bytes).
`nm --defined-only` on that binary finds 82 unique `rt_cranelift_*` symbols
(the 2026-07-11 Linux seed documented above had 68), and all 10 externs named
in this entry are present, including the later-added
`rt_cranelift_new_aot_module_triple`:

- rt_cranelift_call_arg, rt_cranelift_call_args_clear,
  rt_cranelift_data_addr_in_func, rt_cranelift_declare_global_data,
  rt_cranelift_declare_string_data, rt_cranelift_emit_object_raw,
  rt_cranelift_fdemote, rt_cranelift_fpromote,
  rt_cranelift_function_addr_in_func, rt_cranelift_new_aot_module_triple —
  all PRESENT.

The root cause this entry names — "the deployed seed simply predates them" —
is therefore fixed: the current pinned seed was built from source that
exports the full cranelift SFFI surface, exactly the fix the entry
prescribed (redeploy from current source).

End-to-end re-verification of `native-build --backend=cranelift` was
attempted once on this Windows host and is blocked by a SEPARATE, known
defect: release/1.0.0 HEAD is source/binary inconsistent — commit
cfd89933699 added `@representation_boundary` annotations the pinned seed
rejects, so the build dies at
`error: semantic: src/app/cli/native_build_main.spl:239:1: unknown decorator '@representation_boundary'`
(rc=1) before any cranelift SFFI call is reached. The probe log shows the
failure is the decorator, not `unknown extern function: rt_cranelift_*`.
Once the seed/source inconsistency is resolved, the parity harness's
`cranelift_seed_supported()` probe should pass unmodified, as this entry
predicted.
