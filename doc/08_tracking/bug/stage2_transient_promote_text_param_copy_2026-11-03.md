# Frozen stage2 compiles `transient_promote<T>(mut value: T)` for T=text as "promote a fresh COPY" (caller's text freed at scope end)

- **ID:** stage2_transient_promote_text_param_copy_2026-11-03
- **Priority:** P1 (phase 3: every text digest computed inside an owned transient scope is a use-after-free;
  first seen as `capsule-identity-mismatch` on the stage3 hello build)
- **Status:** open. No source workaround landed yet (see below); link-level interim in
  `C:/dev/p3new/s3new/fable_patched/aot-7344b2ef...o`.

## Symptom
Stage3 hello build (HIR cache off, MIR + env patches applied) fails codegen with
`AOT compile error ...: capsule-identity-mismatch`. Minidump `veh_85952.dmp` taken at `_aot_compile_failure`
entry shows the frozen capsule's `mir_identity` field holding `{"params":[],"return_type":"Unit",...}` (a
MIR JSON fragment allocated later) instead of the sha256 digest, while every other compared field matches
(`backend_name`, `target`, `opt_level` 3, `is_release`, `provider_receipt_hash` same pointer on both sides).

## Root cause
`native_capsule_mir_identity_v1` computes the digest inside `transient_scope_begin()`, calls
`transient_promote(digest)`, ends the scope and returns `digest`. In the stage2-built object for
`std.nogc_sync_mut.sffi.transient` (`aot-7344b2ef...`) the `$str` specialization of
`fn transient_promote<T>(mut value: T)` is

```
rt_interp_cstr(value) ; rt_strlen ; rt_string_new(copy) ; rt_transient_heap_promote(COPY)
```

i.e. the `mut` text parameter is re-materialized and the COPY is promoted; the caller's string stays
scope-owned and is freed by `transient_scope_end()`. `$opt_T1` and `$arr_str` pass the value straight
through, so only text roots are affected. This is the text analogue of
`transient_promote_struct_param_copy_dangles_2026-10-25` (which is why `mut` was added).

## Workaround
Interim (link level): patch the `$str` body so `rt_transient_heap_promote` receives the original `rcx`
(`fable_patched/aot-7344b2ef...o`, relinked as `s3_fable6.exe`). A source workaround needs a text-specific
promote that does not copy (e.g. a non-`mut`, non-generic `transient_promote_text(value: text)` used at
text roots); not landed in this change because the call sites are spread across the stdlib/driver.

## Removal condition
A stage2 that passes a `mut` text parameter by handle (no re-materialization).
