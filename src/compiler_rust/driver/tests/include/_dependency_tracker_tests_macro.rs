// Feature #115: Macro Auto-Import Tests
// =============================================================================

#[test]
fn macro_glob_doesnt_leak() {
    // Formal model theorem: glob_doesnt_leak_macros_wf
    let mut manifest = MacroDirManifest::new("test");
    manifest.add_auto_import(AutoImport::new("router", "route")); // Only route

    let mut exports = MacroExports::new();
    exports.add_non_macro(MacroSymbol::value("router", "Router"));
    exports.add_macro(MacroSymbol::macro_def("router", "route")); // In auto import
    exports.add_macro(MacroSymbol::macro_def("router", "get")); // NOT in auto import

    let result = glob_import(&manifest, &exports);

    // Router should be included (non-macro)
    assert!(result.iter().any(|s| s.name == "Router"));

    // route should be included (in auto import)
    assert!(result
        .iter()
        .any(|s| s.name == "route" && s.kind == SymKind::Macro));

    // get should NOT be included (not in auto import)
    assert!(!result.iter().any(|s| s.name == "get"));
}

#[test]
fn macro_nonmacros_always_globbed() {
    // Formal model theorem: nonmacros_always_globbed
    let manifest = MacroDirManifest::new("test"); // Empty auto imports

    let mut exports = MacroExports::new();
    exports.add_non_macro(MacroSymbol::value("mod", "Foo"));
    exports.add_non_macro(MacroSymbol::value("mod", "Bar"));
    exports.add_non_macro(MacroSymbol::value("mod", "Baz"));

    let result = glob_import(&manifest, &exports);

    // All non-macros should be present
    assert!(result.iter().any(|s| s.name == "Foo"));
    assert!(result.iter().any(|s| s.name == "Bar"));
    assert!(result.iter().any(|s| s.name == "Baz"));
}

#[test]
fn macro_auto_imported_in_glob() {
    // Formal model theorem: auto_imported_in_glob
    let mut manifest = MacroDirManifest::new("test");
    manifest.add_auto_import(AutoImport::new("mod", "my_macro"));

    let mut exports = MacroExports::new();
    exports.add_macro(MacroSymbol::macro_def("mod", "my_macro"));

    let result = glob_import(&manifest, &exports);

    assert!(result
        .iter()
        .any(|s| s.name == "my_macro" && s.kind == SymKind::Macro));
}

#[test]
fn macro_empty_auto_import_no_macros() {
    // Formal model theorem: empty_auto_import_no_macros
    let manifest = MacroDirManifest::new("test"); // Empty

    let mut exports = MacroExports::new();
    exports.add_macro(MacroSymbol::macro_def("mod", "macro1"));
    exports.add_macro(MacroSymbol::macro_def("mod", "macro2"));

    let auto_macros = auto_imported_macros(&manifest, &exports);
    assert!(auto_macros.is_empty());

    let result = glob_import(&manifest, &exports);
    // No macros in result
    assert!(result.iter().all(|s| s.kind != SymKind::Macro));
}

#[test]
fn macro_explicit_import_always_works() {
    // Formal model property: explicit imports always work
    let mut exports = MacroExports::new();
    exports.add_non_macro(MacroSymbol::value("mod", "Foo"));
    exports.add_macro(MacroSymbol::macro_def("mod", "my_macro"));

    // Can explicitly import non-macro
    let foo = explicit_import(&exports, "Foo");
    assert!(foo.is_some());
    assert_eq!(foo.unwrap().kind, SymKind::ValueOrType);

    // Can explicitly import macro (even if not in auto import)
    let my_macro = explicit_import(&exports, "my_macro");
    assert!(my_macro.is_some());
    assert_eq!(my_macro.unwrap().kind, SymKind::Macro);

    // Non-existent returns None
    assert!(explicit_import(&exports, "nonexistent").is_none());
}

#[test]
fn macro_is_auto_imported_checks_kind() {
    let mut manifest = MacroDirManifest::new("test");
    manifest.add_auto_import(AutoImport::new("mod", "foo"));

    // Non-macro with same name is NOT auto-imported
    let non_macro = MacroSymbol::value("mod", "foo");
    assert!(!is_auto_imported(&manifest, &non_macro));

    // Macro with correct name IS auto-imported
    let macro_def = MacroSymbol::macro_def("mod", "foo");
    assert!(is_auto_imported(&manifest, &macro_def));
}

// =============================================================================
