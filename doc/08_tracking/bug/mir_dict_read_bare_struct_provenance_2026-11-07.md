# MIR dict-read struct value provenance registered the bare struct name

- **ID:** mir_dict_read_bare_struct_provenance_2026-11-07
- **Severity:** P1 (blocks Stage 2 `compiler_cli_build`)
- **Status:** fix-implemented-verification-pending
- **Found by:** sanctioned bootstrap run 13 (`5fdf9fa`), shards 2-7 of `compiler_cli_build`

## Symptom

116 MIR lowering errors in two files:

- `src/os/smf/smf_dynlib.spl` (80): `ambiguous struct/class field owner
  'DynSmfLoadedLibrary': no module-qualified type provenance` and
  `field '<f>' on ambiguous struct/class owner 'DynSmfLoadedLibrary': no exact layout`
- `src/compiler/99.loader/loader/module_loader.spl` (36): the same for `LoadedModule`.

Every site reads a struct out of a `Dict<K, OwnStruct>` (`val loaded =
DYNSMF_LIBRARIES[h]`, `val module = self.modules[path]`) and then reads a field.

## Not a duplicate definition

The same-named structs are distinct live types, not merge duplicates:
`os.smf.smf_dynlib.DynSmfLoadedLibrary` (module-private struct, mapping
receipts) vs `os.smf.dynsmf_session.DynSmfLoadedLibrary` (exported class,
session view); `compiler.loader.module_loader.LoadedModule` (`reader:
SmfReaderImpl`) vs `module_loader_compat.LoadedModule` (`reader: text`,
`exec_mappings`). Each has its own consumers. The source is correct.

## Root cause

`mir_struct_symbol_name` (`src/compiler/50.mir/_MirLowering/module_lowering.spl`)
returned the BARE struct name for value provenance (dict reads, module-global
struct reads, `Dict.keys()/values()` element tags). The dict value type is a
canonical MIR id (>= 1000000000) that is not in the HIR symbol table, so the
canonical inverse was taken and stripped to its last segment. Because another
module declares a same-named struct with a different field list, the bare
name is conflict-warned and `resolve_field_index` / `resolve_base_struct_name`
fail closed.

## Fix

Value provenance prefers the module-qualified declaration layout key: the
symbol-table path uses `struct_value_provenance_key`, and the canonical path
folds `<module>::<Name>` through `declared_struct_layout_key`. The bare name
is kept only when no unambiguous qualified layout is registered.

Spec: `test/01_unit/compiler/50.mir/dict_read_struct_owner_provenance_spec.spl`
(red 1/6 -> green 6/6 on the seed-hosted in-process harness, including a negative case: a field only the OTHER
same-named struct declares is rejected against the exact layout).

## Verification pending

The run-13 Stage 2 binary embeds the unfixed compiler, so it cannot verify
the source fix; the next bootstrap Stage 2 build closes this row.
