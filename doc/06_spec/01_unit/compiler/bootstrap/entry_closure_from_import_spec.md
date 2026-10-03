# Entry closure from-import dependencies

Manual companion to
`test/01_unit/compiler/bootstrap/entry_closure_from_import_spec.spl`.
Execution status: UNRUN; this is a test plan, not generated passing evidence.

1. Scan the interpreter entry's three bare sibling from-imports. The dependency
   list must be exactly `core`, `parser`, `ast_convert`, in source order.
2. Scan explicit relative and fully qualified paths after a Unicode comment,
   including a multiline import list. Preserve each complete module path.
3. Scan commented/documented imports and a malformed from line. Only the actual
   `real.owner` declaration contributes a dependency.
4. Mix use, from-import, import and export-from declarations. Keep all four
   module paths in source order.

Native integration fixture:
`test/fixtures/bootstrap_builder/from_import_closure/main.spl`. Its two sibling
modules compute 42; successful compilation alone is insufficient. Require
successful execution and `FROM_IMPORT_CLOSURE_NATIVE_PASS`.
