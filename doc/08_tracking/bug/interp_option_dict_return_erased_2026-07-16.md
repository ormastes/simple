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

## Verification (2026-07-17)

Runtime repro at tip 9feac6ef6e5: **IN-CONTEXT REPRO CONFIRMED**.

Followed the doc's prescribed method: temporarily added the `_probe_opt_dict()`
function to `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`
(right after the `CL_TYPE_*` constants block), then ran
`bin/simple native-build --entry probe04c_class_mut_simple.spl --backend cranelift`
(any entry works — the probe fires at module-load time for the whole compiler graph).

Output (`probe08_build.log`):
```
PROBE_OPT_DICT_CHECK=nil
```

Exact match to the doc's quoted `probe check=nil` symptom. The build itself
later failed for an unrelated reason (`unknown extern function:
rt_cranelift_new_aot_module_triple`), irrelevant to this probe which already
captured its answer before that point.

**Status:** STILL-REPRODUCES (exact match, in-context).

## 2026-11-10/11 triage — BLOCKED, needs-grant (lane p3-interp4 row 19, seed-smoke)

Re-verification attempted with this doc's prescribed in-context method on the
worktree seed. Probe added temporarily at the top level of
src/compiler/70.backend/backend/cranelift_codegen_adapter.spl (after the
CL_TYPE_* block), exactly this shape:

    fn _probe_opt_dict() -> Dict<i64, i64>?:
        var h: Dict<i64, i64> = {}
        Some(h)
    val _probe_opt_dict_run = _probe_opt_dict()
    print "PROBE_OPT_DICT_CHECK={_probe_opt_dict_run.?}"

Exact command (worktree C:/Users/yoon/dev/simple-p3-interp4-20261110):

    ./bin/simple.exe native-build --entry examples/01_getting_started/hello_native.spl --backend cranelift

Cycle 1 result: ABANDONED per budget ruling. The run spent >50 min
CPU-saturated (~1 core, ~1.7 GB RSS) in the silent compiler-graph
interpretation phase and was killed by the 3600 s harness task timeout before
the cranelift adapter module initialized (log: build/p3fix-interp4/row19_probe.log,
2518 lines, last line "workarounds: incomplete coverage; run simple check-dbs
--fullscan bugs"; PROBE_OPT_DICT_CHECK never emitted). Per the 2026-11-11
parent directive this cycle was abandoned, not retried unchanged: a full
in-context re-verification needs an UNBOUNDED wall-clock grant (the 2026-07-17
run reached module load quickly; today's graph+seed takes >1 h before any
user-visible phase runs). Standalone `bin/simple run` still does not reproduce
per this doc, so no cheaper repro exists within lane scope.

Status: OPEN, root fix in src/compiler_rust (seed interpreter Option-of-Dict
return channel) — write-forbidden to this lane; routed to the seed-fix lane
together with this grant request. The STATICS_FAILED_KEY workaround in
cranelift_codegen_adapter.spl remains the in-tree mitigation and is unaffected
by the probe (file restored byte-identical to HEAD).
