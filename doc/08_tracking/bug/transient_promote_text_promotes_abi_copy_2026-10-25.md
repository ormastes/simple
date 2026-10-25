# transient_promote$str promotes an extern-ABI copy of its text (2026-10-25)

## Symptom
Phase 3 Stage 3 hello world: `AOT compile error in app.zz_r27_t.h:
capsule-identity-mismatch` (FrozenNativeModuleCapsuleV1.identity_valid false).

## Root cause
`native_capsule_mir_identity_v1` (driver_types.spl) computes the digest inside
a transient scope and calls `transient_promote(digest)`. The Stage-2-compiled
`lib.nogc_sync_mut.sffi.transient.transient_promote$str` marshals its text
argument through the extern text ABI (rt_interp_cstr -> rt_strlen ->
rt_string_new) and passes that FRESH COPY to rt_transient_heap_promote. The copy
is promoted; the original digest is freed by transient_scope_end, so the
capsule's mir_identity field dangles (gdb: header = glibc tcache next/key), and
the expected-identity recompute reads 5 garbage bytes.
Evidence (gdb python): wrapper arg 0x...0520 (data ptr), promote arg 0x...0571
(new object), returned digest 0x...0511 with a freed header.

## Workaround
Binary patch of the wrapper (S/r27/bp/objs/sffi_transient_p3b11.o): replace the
`blr rt_string_new` with `ldr x0, [sp, #0x100]` so the original argument word is
promoted. That word is an untagged data pointer, which the B5 runtime fix
(transient_promote_misses_raw_text_data_pointer_2026-10-25) classifies as its
owning string.

## Compiler fix (open)
Generic externs taking `T` must pass a text handle unchanged, not a
re-materialized copy.

# Lost class field store: session_authority_v2 retained_bytes (same day)
`_backend_session_retain_object_v2`: `owner.retained_bytes = owner.retained_bytes + byte_count`
compiled to a load of field 4 and a store of the sum into a stack temp (the
register holding the object pointer was reused for the temp's address), so the
field stayed 0 and result release failed ByteIntegrityFailed ("backend session
AOT result or compile use could not be released"). Binary patch:
S/r27/bp/objs/session_authority_v2_p3b13.o writes the sum to [owner + 32].
Same class as missing_struct_field_store_writes_field0_2026-10-25.
