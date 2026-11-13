# Non-ASCII before `{` in a string literal corrupts the literal; caches refuse the module

**Status:** FIXED (2026-11-13, branch `work/nonascii-cache-store-20261113`)
**Area:** frontend / string interpolation scanners

## Symptom

Five modules never reached the frontend or HIR cache on any build
(`[frontend-cache] store failed`, `[hir-cache] ... io_failed=1`):
`compiler.backend.llvm_support_matrix`, `plugins.backend_lean.lean_backend`,
`plugins.backend_lean.lean_type_declarations`, `lib.scv.stabilize`,
`lib.scv.shadow`. Each has a string literal with a multibyte character before
an interpolation region, e.g. `"Matrix closure: INCOMPLETE — {errors.len()} ..."`.

## Exact failure

`file_atomic_write` never reached the runtime write (strace: no `openat` for
the entry). gdb on run-21 Stage 2: `external_codec_error` <- 
`external_validate_utf8` <- `external_encode_internal` <- `file_atomic_write`
<- `frontend_parse_cache_store`. The entry carried
`INCOMPLETE \xe2\x80{{{errors.len()}`: the em dash cut after two bytes.

## Root cause

`parse_string_interpolation_regions` and `decode_interpolation_brace_escapes`
(`src/compiler/10.frontend/core/string_interpolation_expand.spl`) and
`flat_bridge_build_string_regions`
(`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`) index the value
by code point (`len()`, `value[i:i+1]`) but cut it with `substring`, which
takes BYTE offsets (owner decision 2026-11-13; Stage 2 and the seed
interpreter). For `"— {n}"`: the region inner became `" "` (fails to parse),
the valid `{n}` region was literalized to `— {{n}`, and the brace decoder cut
that into `\xe2\x80{{{n}` -- invalid UTF-8 in the flat AST, so every cache
encoder rejected it. The program text itself was also wrong (a literal
`{n}` instead of the interpolation).

Minimal fixture: `fn label(n: i64) -> text:\n    "— {n}"`.
Non-ASCII only AFTER the first region (`"{x} → {y}"`) still mis-slices the
later region but happens to stay valid UTF-8, so it stored.

## Fix

Cut with code-point `[a:b]` everywhere the index is a code point; region span
bases add the code-point distance to a char base instead of mixing a byte base
with a code-point index. Spec:
`test/01_unit/compiler/frontend/interpolation_nonascii_unit_spec.spl`
(4/4 red before, 4/4 green after, seed interpreter).
