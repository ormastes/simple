---
id: interp_option_dict_return_erased_2026-07-16
status: OPEN
severity: medium
discovered: 2026-07-16
discovered_by: strict-cranelift diagnosis in scripts/check/check-native-seed-parity.shs
related: src/compiler/70.backend/backend/cranelift_codegen_adapter.spl
---

# Seed interpreter: `-> Dict<K,V>?` return erased to nil in live-interpreted compiler context

## Summary

In the `bin/simple native-build` context (seed interpreting
`src/compiler/*.spl` live), a function returning `Dict<i64, i64>?` loses its
payload: the callee demonstrably executes to its `Some(handles)` tail
expression, yet the caller observes `nil` (`opt.?` interpolates as `nil`,
not even `false`).

Minimal in-context probe (added temporarily to
`cranelift_codegen_adapter.spl`, since a standalone `bin/simple run` file
does NOT reproduce — see below):

```
fn _probe_opt_dict() -> Dict<i64, i64>?:
    var h: Dict<i64, i64> = {}
    Some(h)
# caller in the same file:
val probe = _probe_opt_dict()
print "probe check={probe.?}"     # prints: probe check=nil
```

A plain (non-Option) `-> Dict<i64, i64>` return works correctly in the same
context (payload and entries intact).

## Non-repro in isolation

The identical pattern in a standalone script run via
`env -u SIMPLE_BOOTSTRAP bin/simple run file.spl` returns `Some` correctly
(`.?` == true, for both empty and non-empty dicts). The erasure only
manifests when the full compiler module graph is loaded (native-build
interpreting the backend adapters). Likely the same tag-box/ANY-channel
family as the known seed landmines (Option<i64> tag-box boxing,
Dict.get()->nil on present keys).

## Impact and workaround

`cranelift_compile_module_direct` failed with "Failed to declare module
statics" for EVERY module (even with zero statics) because
`declare_module_statics(...) -> Dict<i64,i64>?` always arrived as nil.
Worked around in cranelift_codegen_adapter.spl by returning a plain
`Dict<i64, i64>` with sentinel key `STATICS_FAILED_KEY = -1` on failure, and
splitting the `-> i64?` accessor `cranelift_static_init_bits` into a
`cranelift_static_init_supported -> bool` / `cranelift_static_init_bits_value
-> i64` pair. Root fix belongs in the seed interpreter's Option-of-Dict
return channel; audit other live-interpreted `-> Dict<...>?` returns in the
backend layer when fixing.
