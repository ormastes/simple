# native_dict_get_text_if_val_double_decode_2026-11-06

**Status:** fix-implemented-verification-pending (P1)

## Symptom
Native (stage3) `val f = d.get(k); if val sn = f:` on a `Dict<K, text>` gave a
wild `sn`; `sn != ""` faulted in `rt_text_eq_any` (p4 q0025 AV in
`note_container_elem_type`). #7168 rewrote that one call site to `?? ""`.

## Root cause
`lower_dict_runtime_read(..., as_option=true)` decodes a text hit with
`rt_interp_cstr` (flat nil 3 preserved on a miss) but records the local's HIR
type as `Optional(Str)`. `decode_present_collection`'s `Str` arm then treated it
as an undecoded option and ran `rt_unwrap_or_self` + `rt_interp_cstr` again on
the `char*`.

## Fix
`MirLowering.decoded_text_option_locals` marker: set at the dict read, copied
through `val`/`var` bindings and assignment (cleared on reassignment from an
unmarked value), reset per function, released with the transient owner roots.
The present edge copies a marked local instead of decoding it again.

## Tests
- `test/01_unit/compiler/50.mir/dict_get_text_if_val_single_decode_spec.spl`
  (source pins + hit/miss of bound, direct and reassigned if-val).
- Sibling class: `scripts/check/check-class-field-dict-bracket-read.shs`.

## Verify (pending)
`s3_fable46.exe` copy SEGVs rc=139 before diagnostics on the fixture. Rebuild
stage3 from this source, then `native-build --entry-closure` a fixture with
`class N: syms: Dict<i64, text>`, `n.syms[7] = "Point"`,
`if val sn = n.syms.get(7): print "hit:" + sn` and expect `hit:Point`.
