# HIR cache codec self-check rejects entries: nil_in_non_optional_scalar

- Date: 2026-10-25
- Status: OPEN (filed, not fixed)
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
