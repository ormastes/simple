# Seed JIT field-type inference resolves struct fields by bare struct name across modules

Status: open (worked around in the library by renaming one struct).

Repro (base e979821505b, seed sha256 prefix 5bdd376460541de9):
`SIMPLE_EXECUTION_MODE=jit seed run test/01_unit/lib/common/zstd_compressed_block_spec.spl` prints
`[jit-fallback] HIR lowering error: Cannot infer field type: struct 'ZstdFrameHeader' field 'dict_id'
(declared fields: bytes_used, checksum_flag, window_size, content_size, dictionary_id)` and the whole module drops to
the interpreter. Two unrelated structs share the name `ZstdFrameHeader`:
`src/lib/common/compress/zstd_types.spl` and (before the rename) `src/lib/nogc_sync_mut/compression/zstd/frame.spl`
(constructor with `dict_id:` at frame.spl:141). The lookup (`hir/lower/type_resolver.rs`, CannotInferFieldType sites)
uses the other module's declaration.

Workaround applied: `frame.spl` struct renamed `ZstdLegacyFrameHeader`. Proper fix: key struct registries by
module-qualified name in the Rust seed HIR lowering. The pure-Simple compiler (`src/compiler/`) was not audited.
