# HIR cache codec self-check rejects entries: nil_in_non_optional_scalar

- Date: 2026-10-25
- Status: FIX LANDED (pending stage-3 rerun confirmation)
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
