// Feature #116: Symbol Resolution Tests
// =============================================================================

#[test]
fn symbol_table_basic() {
    let mut table = SymbolTable::new("crate.foo");

    let entry = SymbolEntry::local(
        "Bar",
        "crate.foo.Bar",
        SymbolKind::Type,
        Visibility::Public,
        "crate.foo",
    );

    assert!(table.define(entry).is_ok());
    assert!(table.contains("Bar"));

    let looked_up = table.lookup("Bar").unwrap();
    assert_eq!(looked_up.qualified_name, "crate.foo.Bar");
    assert!(looked_up.is_public());
}

#[test]
fn symbol_table_conflict_detection() {
    let mut table = SymbolTable::new("crate.foo");

    let entry1 = SymbolEntry::local(
        "Bar",
        "crate.foo.Bar",
        SymbolKind::Type,
        Visibility::Public,
        "crate.foo",
    );

    let entry2 = SymbolEntry::local(
        "Bar",
        "crate.foo.Bar2",
        SymbolKind::Function,
        Visibility::Public,
        "crate.foo",
    );

    assert!(table.define(entry1).is_ok());
    assert!(table.define(entry2).is_err()); // Conflict
}

#[test]
fn symbol_table_visibility_filtering() {
    let mut table = SymbolTable::new("crate.foo");

    table.define_or_replace(SymbolEntry::local(
        "PublicFn",
        "crate.foo.PublicFn",
        SymbolKind::Function,
        Visibility::Public,
        "crate.foo",
    ));

    table.define_or_replace(SymbolEntry::local(
        "PrivateFn",
        "crate.foo.PrivateFn",
        SymbolKind::Function,
        Visibility::Private,
        "crate.foo",
    ));

    let public: Vec<_> = table.public_symbols().collect();
    assert_eq!(public.len(), 1);
    assert_eq!(public[0].name, "PublicFn");
}

#[test]
fn symbol_table_macro_filtering() {
    let mut table = SymbolTable::new("crate.foo");

    table.define_or_replace(SymbolEntry::local(
        "my_func",
        "crate.foo.my_func",
        SymbolKind::Function,
        Visibility::Public,
        "crate.foo",
    ));

    table.define_or_replace(SymbolEntry::local(
        "my_macro",
        "crate.foo.my_macro",
        SymbolKind::Macro,
        Visibility::Public,
        "crate.foo",
    ));

    let macros: Vec<_> = table.macros().collect();
    assert_eq!(macros.len(), 1);
    assert_eq!(macros[0].name, "my_macro");
}

#[test]
fn project_symbols_qualified_lookup() {
    let mut project = ProjectSymbols::new();

    {
        let table = project.get_or_create("crate.foo");
        table.define_or_replace(SymbolEntry::local(
            "Bar",
            "crate.foo.Bar",
            SymbolKind::Type,
            Visibility::Public,
            "crate.foo",
        ));
    }

    {
        let table = project.get_or_create("crate.baz");
        table.define_or_replace(SymbolEntry::local(
            "Qux",
            "crate.baz.Qux",
            SymbolKind::Function,
            Visibility::Public,
            "crate.baz",
        ));
    }

    // Qualified lookup
    let bar = project.lookup_qualified("crate.foo.Bar");
    assert!(bar.is_some());
    assert_eq!(bar.unwrap().name, "Bar");

    let qux = project.lookup_qualified("crate.baz.Qux");
    assert!(qux.is_some());
    assert_eq!(qux.unwrap().name, "Qux");

    // Non-existent
    assert!(project.lookup_qualified("crate.nonexistent.X").is_none());
}

#[test]
fn symbol_imported_vs_local() {
    let mut table = SymbolTable::new("crate.foo");

    // Local symbol
    table.define_or_replace(SymbolEntry::local(
        "LocalFn",
        "crate.foo.LocalFn",
        SymbolKind::Function,
        Visibility::Public,
        "crate.foo",
    ));

    // Imported symbol
    table.define_or_replace(SymbolEntry::imported(
        "ImportedType",
        "crate.bar.ImportedType",
        SymbolKind::Type,
        Visibility::Public,
        "crate.bar",
    ));

    let local: Vec<_> = table.local_symbols().collect();
    assert_eq!(local.len(), 1);
    assert_eq!(local[0].name, "LocalFn");
    assert!(!local[0].is_imported);

    let imported = table.lookup("ImportedType").unwrap();
    assert!(imported.is_imported);
}

#[test]
fn symbol_aliased_import() {
    let entry = SymbolEntry::aliased(
        "MyAlias",
        "OriginalName",
        "crate.foo.OriginalName",
        SymbolKind::Type,
        Visibility::Public,
        "crate.foo",
    );

    assert_eq!(entry.name, "MyAlias");
    assert_eq!(entry.original_name, Some("OriginalName".to_string()));
    assert!(entry.is_imported);
}

// =============================================================================
// Integration Tests: Combined Features
// =============================================================================

#[test]
fn integration_module_with_visibility_and_exports() {
    // Create a realistic module structure
    let mut manifest = DirManifest::new("http");
    manifest.add_child(ModDecl::public("router"));
    manifest.add_child(ModDecl::private("internal"));
    manifest.add_export(SymbolId::new("Router"));
    manifest.add_export(SymbolId::new("route"));

    // Router module contents
    let mut router_contents = ModuleContents::new();
    router_contents.add_symbol(Symbol::public("Router"));
    router_contents.add_symbol(Symbol::public("route"));
    router_contents.add_symbol(Symbol::private("helper"));

    // Internal module contents
    let mut internal_contents = ModuleContents::new();
    internal_contents.add_symbol(Symbol::public("InternalHelper"));

    // Check visibility
    assert_eq!(
        effective_visibility(
            &manifest,
            "router",
            &router_contents,
            &SymbolId::new("Router")
        ),
        Visibility::Public
    );
    assert_eq!(
        effective_visibility(
            &manifest,
            "router",
            &router_contents,
            &SymbolId::new("route")
        ),
        Visibility::Public
    );
    assert_eq!(
        effective_visibility(
            &manifest,
            "router",
            &router_contents,
            &SymbolId::new("helper")
        ),
        Visibility::Private
    );
    assert_eq!(
        effective_visibility(
            &manifest,
            "internal",
            &internal_contents,
            &SymbolId::new("InternalHelper")
        ),
        Visibility::Private // Private module
    );
}

#[test]
fn integration_glob_import_with_auto_import() {
    // Simulate: common use router.*
    // With auto_import router.route

    let mut macro_manifest = MacroDirManifest::new("http");
    macro_manifest.add_auto_import(AutoImport::new("router", "route"));

    let mut exports = MacroExports::new();
    exports.add_non_macro(MacroSymbol::value("router", "Router"));
    exports.add_non_macro(MacroSymbol::value("router", "Request"));
    exports.add_macro(MacroSymbol::macro_def("router", "route"));
    exports.add_macro(MacroSymbol::macro_def("router", "get"));
    exports.add_macro(MacroSymbol::macro_def("router", "post"));

    let result = glob_import(&macro_manifest, &exports);

    // Non-macros: Router, Request
    assert!(result.iter().any(|s| s.name == "Router"));
    assert!(result.iter().any(|s| s.name == "Request"));

    // Auto-imported macro: route
    assert!(result
        .iter()
        .any(|s| s.name == "route" && s.kind == SymKind::Macro));

    // NOT included: get, post (not in auto import)
    assert!(!result.iter().any(|s| s.name == "get"));
    assert!(!result.iter().any(|s| s.name == "post"));

    // Total: 2 non-macros + 1 macro = 3
    assert_eq!(result.len(), 3);
}

#[test]
fn integration_import_graph_with_symbols() {
    // Build an import graph and symbol tables together
    let mut graph = ImportGraph::new();
    let mut symbols = ProjectSymbols::new();

    // crate.main imports crate.lib and crate.utils
    graph.add_use("crate.main", "crate.lib");
    graph.add_use("crate.main", "crate.utils");

    // crate.lib imports crate.utils
    graph.add_use("crate.lib", "crate.utils");

    // No cycles
    assert!(graph.check_cycles().is_ok());

    // Add symbols
    {
        let main_table = symbols.get_or_create("crate.main");
        main_table.define_or_replace(SymbolEntry::local(
            "main",
            "crate.main.main",
            SymbolKind::Function,
            Visibility::Public,
            "crate.main",
        ));
    }

    {
        let lib_table = symbols.get_or_create("crate.lib");
        lib_table.define_or_replace(SymbolEntry::local(
            "process",
            "crate.lib.process",
            SymbolKind::Function,
            Visibility::Public,
            "crate.lib",
        ));
    }

    {
        let utils_table = symbols.get_or_create("crate.utils");
        utils_table.define_or_replace(SymbolEntry::local(
            "helper",
            "crate.utils.helper",
            SymbolKind::Function,
            Visibility::Public,
            "crate.utils",
        ));
    }

    // Check transitive imports
    let trans = graph.transitive_imports("crate.main");
    assert!(trans.contains("crate.lib"));
    assert!(trans.contains("crate.utils"));

    // Check symbol lookup
    assert!(symbols.lookup_qualified("crate.lib.process").is_some());
    assert!(symbols.lookup_qualified("crate.utils.helper").is_some());
}
