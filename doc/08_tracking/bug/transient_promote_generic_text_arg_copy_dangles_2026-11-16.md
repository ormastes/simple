# Transient promote of a call-result text promotes a copy; the original dangles (2026-11-16)

Bug id: `s2-transient-promote-dangle`. Blocks the Stage 3 -> Stage 3 self-build
(the integ2-built Stage 3 needs a no-op transient shim, which never reclaims and
OOMs the 1531-file build).

## Symptom

`FrozenNativeModuleCapsuleV1.mir_identity` reads back as an unrelated string
literal -> capsule-identity-mismatch / capsule-mir-lease-violated. Minimal
repro (diaglink `rep3/transient3.spl`): V1 len 29 want 24, V2/V3 len 3-4 want
64, on cranelift and llvm, integ2 AND integ3 Stage 2.

## Root cause

`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, direct-call
argument loop, `case HirTypeKind.Any | HirTypeKind.TypeParam` boxed the argument
with `box_runtime_value`. Its `local_is_str` arm (`expr_dispatch.spl`) copies
every text local that lacks a static tagged-text note -- every call result --
as `rt_string_new(rt_interp_cstr(v), rt_strlen(..))`. Disassembly of
`v_direct_sha` (integ2): `rt_interp_cstr -> rt_strlen -> rt_string_new ->
rt_transient_heap_promote`, then `ldr x0,[x20]` returns the original. gdb: the
original word is a tagged handle (`...761`, `RTS\002` header).

The copy is allocated in the PAUSED window (owner scope 0 = persistent), so
promote is a no-op success; scope end frees the original the caller returns.
Live site: `native_capsule_mir_identity.spl:303`
`transient_promote<text>(digest)` with `digest` a call result.

## Fix

The Any/TypeParam boundary uses `box_runtime_dictionary_key_v1`: it asks
`rt_string_data` at run time and copies only a borrowed `char*`; a tagged
handle passes through with its identity. Non-text arguments are unchanged.
Spec: `test/01_unit/compiler/mir/generic_text_arg_identity_spec.spl`.

Coverage (gdb on the integ2 base binary, word at the boxing site):

| shape | word | dangles on integ2 | closed by this fix |
|---|---|---|---|
| call result (`val d = f()`) | tagged `...761` | yes (V1-V3) | yes |
| struct field load (`fact.kind`) | tagged `...4b1` | yes (V8) | yes |
| `[text]` element (`xs[i]`) | raw `char*` `...790` | yes (V9) | **no** -- borrowed branch still copies |

Open: a `[text]` element is a bare data pointer, so the run-time probe cannot
tell it from a literal and still materializes a copy. Promoting the owning
array (the usual pattern, e.g. `reverse_reference_facts.spl`) is unaffected,
because the array walk reaches the original word.

Ownership note: a tagged text now reaches a generic callee by reference rather
than as a persistent copy, so a callee that stores it during a paused window
stores the transient original. Statically tagged locals already behaved this
way; the change only removes the dependence on the static note.

Separate, not transient: interpolating a `sha256_text` result
(`print "[{a}]"`, no transient scope at all) prints garbage and drops the rest
of the line under integ2 Stage 2, so `rep3/transient2.spl` stays DIFF even
with the full no-op shim.

Takes effect only after a Stage 2 is rebuilt with it. Until then: diaglink
`s3i2/shim_transient_narrow.c` (real scopes; re-promotes the source of the
last `rt_string_new` copies) or the root-site source rewrite recorded in the
Stage 3 lane notes.
