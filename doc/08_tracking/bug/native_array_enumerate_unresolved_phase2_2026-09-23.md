# Native `Array.enumerate` unresolved in Phase 2 LSP build

Exact source `8b131cbf1c64ebf9034700e4369a015777b35f45` fails the Windows Phase 2 LSP native build at `src/app/cli/query_rich_common.spl:146`:

> llvm codegen: semantic: cannot resolve method call `Array.enumerate`: receiver is a builtin type but `enumerate` is neither a known runtime method nor a resolvable user definition

The expression was `value.chars().enumerate()`. The interpreter accepts this compact indexed iteration, but the admitted Stage 2 native compiler cannot lower it. Native support for indexed array iteration should either resolve the standard method with correct index/value types or reject it at check time with a targeted diagnostic. The query serializer now uses byte indexed iteration because its `substring` spans and `text.len()` are byte based; this unblocks the LSP build without changing its output. The compact form remains a compiler/library bug, not an accepted limitation of the language.

Regression: `test/01_unit/app/cli/query_json_escape_native_spec.spl` covers unchanged Unicode, adjacent escapes, and UTF-8 text on both sides of escapes. Re-run the isolated LSP native build with `SIMPLE_NO_STUB_FALLBACK=1` to verify the Phase 2 shard.
