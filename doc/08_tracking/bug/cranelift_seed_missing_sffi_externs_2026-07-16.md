---
id: cranelift_seed_missing_sffi_externs_2026-07-16
status: OPEN
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
