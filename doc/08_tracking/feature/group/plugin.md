# plugin

## Features

| ID | Feature | Description | Modes | Platforms | Spec |
|----|---------|-------------|-------|-----------|------|
| <a id="feature-FR-PLUG-0002-2"></a>FR-PLUG-0002-2 | FR-PLUG-0002 (structural) — `.so` block-proxy constructor | Implemented in pure Simple. `_SoBlockProxy(BlockDefinition)` struct added to `src/compiler/15.blocks/plugin_startup.spl`. `activate_plugin` now dlsyms `<ClassName>_keyword` and `<ClassName>_parse` for each `block:` function entry, construct | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| <a id="feature-FR-PLUG-0003-2"></a>FR-PLUG-0003-2 | FR-PLUG-0003 (structural) — Sugar registry AST round-trip | Implemented in pure Simple: - `DesugarRule` extended with `ast_rewrite_fn: i64` in `sugar_registry.spl` - `apply_rule_ast` and `apply_sugar_rules_ast` functions added to `sugar_registry.spl` - `desugar_collections` loop in `collection_desug | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
| <a id="feature-FR-PLUG-0004-2"></a>FR-PLUG-0004-2 | FR-PLUG-0004 (verification only) — Static lowering markers | Pure-Simple verification added to `test/03_system/feature/plugin/sugar_plugin_spec.spl` for the `[STATIC-NEXT]` handoff markers in the sugar registry, collection desugar loop, and backend matmul lowering site. Backend fusion remains open. # | interpreter:supported, jit:supported, smf_cranelift:supported, smf_llvm:supported | - | - |
