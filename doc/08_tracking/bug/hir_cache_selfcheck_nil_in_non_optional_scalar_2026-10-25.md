# HIR cache codec self-check rejects entries: nil_in_non_optional_scalar

- Date: 2026-10-25
- Status: FIX 2 (first fix insufficient; pending stage-3 rerun confirmation)
- Seen in: ad-hoc Stage 3 (frozen admitted Stage 2 compiling the
  `src/app/cli/bootstrap_main.spl` closure, 1453 modules, Windows
  x86_64-pc-windows-gnu), logs `build/s3-mine/build.log`,
  `build/s3-bis-aeA/build.log`, `build/s3-bis-cmA/build.log` in the
  `wt-rel3-new` worktree.

## Symptom

313 lines like:

```
[hir-cache] SELFCHECK FAILED module=src/compiler/00.common/diagnostics/span.spl ... reason=decode bytes=60349 cause=reader kind=malformed detail=nil_in_non_optional_scalar line=7711/11766 token=N; entry not stored
```

The encoder writes a nil token (`N`) where the generated decoder
(`src/compiler/20.hir/generated/hir_codec.spl:152-164`, scalar readers)
requires a non-optional scalar. The round-trip self-check then refuses to
store the entry, so the shard's HIR work is recomputed / not reusable.
Estimated ~85% of HIR shard work is wasted on this run.

## Likely cause (unverified)

A HIR field declared non-optional in the codec schema carries nil at
encode time under native Stage 2 (uninitialized/defaulted field, or a
schema/type mismatch between the HIR definition and the generated codec).
The failing line index points at the specific field; decode one failing
entry with the reported `line=` to name it.

## Next step

Name the field from `line=` for `span.spl`, then fix either the producer
(never leave it nil) or the schema (make it optional). Do not loosen the
self-check.

## Root cause (2026-10-25, static analysis)

`HirImpl.method_return_is_array` / `method_return_is_optional` are
`Dict<text, bool>`. The generated encoder read them as
`w.put_bool(node.method_return_is_array[dk])`. Under staged-native codegen
the field-projection temp is typed i64, so `lower_dict_runtime_read` resolves
the dict value type as i64 and decodes the bool word with the integer `>>3`
arm (11 -> 1, 0 -> 0). `HirCodecWriter.put_bool` renders `"{v}"` and maps only
`true`/`false`, so `1`/`0` were written as `N`, and the decoder's
`nil_in_non_optional_scalar` guard refused the entry. Every module with an
`impl` that has methods hit it right after the impl's inline `methods` list,
matching the varying `line=` offsets.

## Fix

`src/app/compiler_schema/codec_gen.spl` now emits a typed
`val dmK: Dict<K, bool> = <field>` local for every Dict<_, bool> value read;
the generated `hir_codec.spl` was updated to the same text (2 sites). The
self-check was not loosened. Spec:
`test/01_unit/app/compiler_schema/hir_codec_nil_scalar_reject_spec.spl`
("HIR codec Dict<_, bool> encode"). Not yet confirmed by a native stage
rerun: no runnable pure-Simple binary was available on this host for the
current source (the seed rejects current stdlib).

## Fix 1 insufficient (2026-10-25, later)

Stage 2 built at `d72188e68ec` (contains fix 1, `184d31e1c69`) still logged
313 `SELFCHECK FAILED ... nil_in_non_optional_scalar token=N` in
`wt-rel3-new/build/s3-perfile2/build.log` (hits=239/1495). The typed local
still yields the int-decoded word 1/0, which `put_bool` renders as neither
`true` nor `false` and writes as `N`. Fix 2: the generator branches on the
value (`if dmK[dkK]: w.put_bool(true) else: w.put_bool(false)`), so only
literals reach `put_bool`. The regenerate also picked up a stale-codec gap:
`HirSymbol.generic_param_count` was not encoded at all (a hit silently lost
it); the checked-in `hir_codec.spl` now matches generator output byte for
byte. Self-check not loosened. Unconfirmed until a stage-3 rerun shows
`selfcheck_failed` near 0 (whether these two Dict<_, bool> fields are the
ONLY N source is not proven -- no failing entry is stored to decode).

## Fix 3 — the real dominant source: omitted desugared `has_X` flags (2026-10-25)

Fix 2 (`6e3dd22dc90`) is NOT in stage2 `d72188e68ec`, so the s3-perfile2/
s3-perfile3/s3-wa logs never exercised it. But it is also not sufficient:
`src/compiler/80.driver/perf/compiler_work_counters.spl` (a lone struct, no
`impl`) fails the same way. Reproduced with that stage2 on 3-line fixtures:
`fn main` only -> stored; `struct P: x: i64` (no impl) -> `refused reason=decode`.

Root cause: HIR lowering constructs nodes with named args but omits the
DESUGARED presence flag that pairs with an optional field. The flag is nil at
runtime, `put_bool` writes `N`, and the decoder guard rejects. A scan of every
`Hir*(` named construction against its non-optional bool/i64 fields found 13
omissions, all `has_*`:

- HirStruct.has_doc_comment, has_specialization_of (declaration_lowering) — every module with a struct
- HirTrait.has_doc_comment, has_specialization_of; HirConst.has_fixed_address;
  HirAssocTypeDecl.has_default; HirBitfieldField.has_type_; HirStaticAssert.has_message (trait_impl_lowering)
- HirField.has_fixed_address; HirBitfield.has_doc_comment (declaration_lowering)
- HirInterpolation.has_format (expression_components); lambda HirParam.has_default (expression_core);
  HirWithItem.has_target (statements)

All now set from the parser's own `has_*` (or `false`/`true` where fixed),
matching class/function lowering. Spec:
`test/01_unit/compiler/20.hir/hir_lowering_desugared_has_flags_spec.spl`.
Needs a stage2 rebuilt at or after this commit to take effect.

## Fix 4 — HirSymbol.generic_param_count field default not applied (2026-10-25)

Stage2 built from `f9d07913dcc` (contains #4785) still refused 799/1515.
Reproduced with that stage2: `struct P: x: i64` and `class K: x: i64` fixtures
-> `SELFCHECK FAILED ... line=496/527 token=N`; fn/enum/trait/default-param
fixtures store fine. The slot is `HirSymbol.generic_param_count: i64 = 0`,
first encoded by fix 2. 13 named `HirSymbol(...)` constructions omit it and
rely on the `= 0` default, which staged-native codegen does not apply to an
omitted named arg -- the slot stays nil and encodes as `N`. All 13 now pass it
explicitly (copies preserve the source value). Spec:
`test/01_unit/compiler/20.hir/hir_symbol_generic_param_count_explicit_spec.spl`.
Underlying codegen gap (struct field defaults dropped on named construction
under staged-native) is still open and is the general form of fixes 3 and 4.

## Root cause located (2026-10-25)

The dropped default is a Rust-seed HIR gap (stage2 is seed-built), not
pure-Simple MIR: see `native_struct_field_default_dropped_on_reexport_2026-10-25.md`.
