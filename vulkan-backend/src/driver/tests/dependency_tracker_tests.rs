//! System tests for dependency tracker (Features #112-117)
//!
//! These tests verify the formally-verified dependency tracking system works
//! correctly with actual filesystem operations and multi-file projects.
//!
//! ## Formal Verification Coverage
//!
//! The tests verify properties proven in the Lean 4 models:
//! - module_resolution: Module paths are unambiguous in well-formed filesystems
//! - visibility_export: Effective visibility is intersection of item and ancestor visibility
//! - macro_auto_import: Glob imports only include macros listed in auto import
//!
//! ## Test Categories
//!
//! 1. Module Resolution - file vs directory module detection
//! 2. Visibility Rules - pub/priv and export filtering
//! 3. Macro Auto-Import - glob import macro filtering
//! 4. Circular Dependency - import cycle detection
//! 5. Symbol Resolution - cross-module symbol lookup

use simple_dependency_tracker::{
    graph::ImportGraph,
    macro_import::{
        auto_imported_macros, explicit_import, glob_import, is_auto_imported, AutoImport,
        MacroDirManifest, MacroExports, MacroSymbol, SymKind,
    },
    resolution::{resolve, well_formed, FileKind, FileSystem, ModPath, ResolutionResult},
    symbol::{ProjectSymbols, SymbolEntry, SymbolKind, SymbolTable},
    visibility::{
        ancestor_visibility, effective_visibility, visibility_meet, DirManifest, ModDecl,
        ModuleContents, Symbol, SymbolId, Visibility,
    },
};
use std::fs;
use std::path::Path;
use tempfile::TempDir;

// =============================================================================
// Test Helpers
// =============================================================================

fn create_test_project() -> TempDir {
    TempDir::new().unwrap()
}

fn create_module_file(dir: &TempDir, path: &str, content: &str) {
    let full_path = dir.path().join(path);
    if let Some(parent) = full_path.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::write(full_path, content).unwrap();
}

// =============================================================================
// Feature #113: Module Resolution Tests
// =============================================================================

#[test]
fn resolution_file_module() {
    let dir = create_test_project();
    create_module_file(&dir, "src/utils.spl", "fn helper(): 42");

    let mut fs = FileSystem::new();
    fs.add_file(dir.path().join("src/utils.spl"));

    let mp = ModPath::parse("utils").unwrap();
    let root = dir.path().join("src");

    match resolve(&fs, &root, &mp) {
        ResolutionResult::Unique { kind, path } => {
            assert_eq!(kind, FileKind::File);
            assert!(path.to_string_lossy().contains("utils.spl"));
        }
        other => panic!("Expected Unique File, got {:?}", other),
    }
}

#[test]
fn resolution_directory_module() {
    let dir = create_test_project();
    create_module_file(&dir, "src/http/__init__.spl", "mod http\npub mod router");

    let mut fs = FileSystem::new();
    fs.add_file(dir.path().join("src/http/__init__.spl"));

    let mp = ModPath::parse("http").unwrap();
    let root = dir.path().join("src");

    match resolve(&fs, &root, &mp) {
        ResolutionResult::Unique { kind, path } => {
            assert_eq!(kind, FileKind::Directory);
            assert!(path.to_string_lossy().contains("__init__.spl"));
        }
        other => panic!("Expected Unique Directory, got {:?}", other),
    }
}

#[test]
fn resolution_nested_module() {
    let dir = create_test_project();
    create_module_file(&dir, "src/sys/http/router.spl", "struct Router:");

    let mut fs = FileSystem::new();
    fs.add_file(dir.path().join("src/sys/http/router.spl"));

    let mp = ModPath::parse("sys.http.router").unwrap();
    let root = dir.path().join("src");

    match resolve(&fs, &root, &mp) {
        ResolutionResult::Unique { kind, path } => {
            assert_eq!(kind, FileKind::File);
            assert!(path.to_string_lossy().contains("router.spl"));
        }
        other => panic!("Expected Unique File, got {:?}", other),
    }
}

#[test]
fn resolution_not_found() {
    let fs = FileSystem::new();
    let mp = ModPath::parse("nonexistent").unwrap();
    let root = Path::new("/fake/path");

    assert!(matches!(
        resolve(&fs, root, &mp),
        ResolutionResult::NotFound
    ));
}

#[test]
fn resolution_ambiguous_detected() {
    // This tests the formal model property: ambiguity is detected
    let dir = create_test_project();
    create_module_file(&dir, "src/foo.spl", "fn foo(): 1");
    create_module_file(&dir, "src/foo/__init__.spl", "mod foo");

    let mut fs = FileSystem::new();
    fs.add_file(dir.path().join("src/foo.spl"));
    fs.add_file(dir.path().join("src/foo/__init__.spl"));

    let mp = ModPath::parse("foo").unwrap();
    let root = dir.path().join("src");

    // Should detect ambiguity
    match resolve(&fs, &root, &mp) {
        ResolutionResult::Ambiguous {
            file_path,
            dir_path,
        } => {
            assert!(file_path.to_string_lossy().contains("foo.spl"));
            assert!(dir_path.to_string_lossy().contains("__init__.spl"));
        }
        other => panic!("Expected Ambiguous, got {:?}", other),
    }

    // Well-formedness check should fail
    assert!(!well_formed(&fs, &root));
}

#[test]
fn resolution_well_formed_filesystem() {
    let dir = create_test_project();
    create_module_file(&dir, "src/foo.spl", "fn foo(): 1");
    create_module_file(&dir, "src/bar/__init__.spl", "mod bar");

    let mut fs = FileSystem::new();
    fs.add_file(dir.path().join("src/foo.spl"));
    fs.add_file(dir.path().join("src/bar/__init__.spl"));

    let root = dir.path().join("src");

    // No ambiguity - well-formed
    assert!(well_formed(&fs, &root));
}

#[test]
fn resolution_crate_prefix() {
    let mp = ModPath::parse("crate.sys.http").unwrap();
    assert!(mp.is_absolute());

    let without_crate = mp.without_crate_prefix().unwrap();
    assert_eq!(without_crate.segments().len(), 2);
    assert_eq!(without_crate.segments()[0].name(), "sys");
    assert_eq!(without_crate.segments()[1].name(), "http");
}

// =============================================================================
// Feature #114: Visibility Export Tests
// =============================================================================

#[test]
fn visibility_private_symbol_stays_private() {
    // Formal model theorem: private_stays_private
    let mut manifest = DirManifest::new("test");
    manifest.add_child(ModDecl::public("mymodule"));
    manifest.add_export(SymbolId::new("foo"));

    let mut mc = ModuleContents::new();
    mc.add_symbol(Symbol::private("foo")); // Private symbol

    let sym = SymbolId::new("foo");
    let vis = effective_visibility(&manifest, "mymodule", &mc, &sym);

    assert_eq!(vis, Visibility::Private);
}

#[test]
fn visibility_private_module_restricts() {
    // Formal model theorem: private_module_restricts
    let mut manifest = DirManifest::new("test");
    manifest.add_child(ModDecl::private("internal")); // Private module
    manifest.add_export(SymbolId::new("Helper"));

    let mut mc = ModuleContents::new();
    mc.add_symbol(Symbol::public("Helper"));

    let sym = SymbolId::new("Helper");
    let vis = effective_visibility(&manifest, "internal", &mc, &sym);

    // Even though symbol is public and exported, module is private
    assert_eq!(vis, Visibility::Private);
}

#[test]
fn visibility_must_be_exported() {
    // Formal model theorem: must_be_exported
    let mut manifest = DirManifest::new("test");
    manifest.add_child(ModDecl::public("router"));
    // NOT adding export for "Helper"

    let mut mc = ModuleContents::new();
    mc.add_symbol(Symbol::public("Helper"));

    let sym = SymbolId::new("Helper");
    let vis = effective_visibility(&manifest, "router", &mc, &sym);

    // Public module, public symbol, but not exported
    assert_eq!(vis, Visibility::Private);
}

#[test]
fn visibility_fully_public() {
    // All conditions met: public module + public symbol + exported
    let mut manifest = DirManifest::new("test");
    manifest.add_child(ModDecl::public("router"));
    manifest.add_export(SymbolId::new("Router"));

    let mut mc = ModuleContents::new();
    mc.add_symbol(Symbol::public("Router"));

    let sym = SymbolId::new("Router");
    let vis = effective_visibility(&manifest, "router", &mc, &sym);

    assert_eq!(vis, Visibility::Public);
}

#[test]
fn visibility_ancestor_chain() {
    // Formal model theorems: any_private_means_private, all_public_means_public

    // All public ancestors
    let path = vec![Visibility::Public, Visibility::Public, Visibility::Public];
    assert_eq!(ancestor_visibility(&path), Visibility::Public);

    // One private ancestor
    let path = vec![Visibility::Public, Visibility::Private, Visibility::Public];
    assert_eq!(ancestor_visibility(&path), Visibility::Private);

    // Empty path (root) is public
    assert_eq!(ancestor_visibility(&[]), Visibility::Public);
}

#[test]
fn visibility_meet_properties() {
    // Formal model theorems: meet_comm, meet_assoc

    // Commutative
    assert_eq!(
        visibility_meet(Visibility::Public, Visibility::Private),
        visibility_meet(Visibility::Private, Visibility::Public)
    );

    // Associative
    let a = Visibility::Public;
    let b = Visibility::Private;
    let c = Visibility::Public;
    assert_eq!(
        visibility_meet(visibility_meet(a, b), c),
        visibility_meet(a, visibility_meet(b, c))
    );

    // Private absorbs
    assert_eq!(
        visibility_meet(Visibility::Private, Visibility::Public),
        Visibility::Private
    );

    // Public is identity
    assert_eq!(
        visibility_meet(Visibility::Public, Visibility::Public),
        Visibility::Public
    );
}

// =============================================================================
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
// Feature #117: Circular Dependency Detection Tests
// =============================================================================

#[test]
fn circular_no_cycle_linear() {
    let mut graph = ImportGraph::new();
    graph.add_use("a", "b");
    graph.add_use("b", "c");
    graph.add_use("c", "d");

    assert!(graph.check_cycles().is_ok());
}

#[test]
fn circular_no_cycle_diamond() {
    // Diamond dependency is NOT a cycle
    let mut graph = ImportGraph::new();
    graph.add_use("a", "b");
    graph.add_use("a", "c");
    graph.add_use("b", "d");
    graph.add_use("c", "d");

    assert!(graph.check_cycles().is_ok());
}

#[test]
fn circular_simple_cycle_detected() {
    let mut graph = ImportGraph::new();
    graph.add_use("a", "b");
    graph.add_use("b", "a");

    let result = graph.check_cycles();
    assert!(result.is_err());

    let err = result.unwrap_err();
    assert!(err.cycle.contains(&"a".to_string()));
    assert!(err.cycle.contains(&"b".to_string()));
}

#[test]
fn circular_triangle_detected() {
    let mut graph = ImportGraph::new();
    graph.add_use("a", "b");
    graph.add_use("b", "c");
    graph.add_use("c", "a");

    assert!(graph.check_cycles().is_err());
}

#[test]
fn circular_self_reference_detected() {
    let mut graph = ImportGraph::new();
    graph.add_use("a", "a"); // Self-reference

    assert!(graph.check_cycles().is_err());
}

#[test]
fn circular_complex_graph_with_cycle() {
    let mut graph = ImportGraph::new();
    // Main chain
    graph.add_use("main", "a");
    graph.add_use("main", "b");
    graph.add_use("a", "c");
    graph.add_use("b", "d");
    // Hidden cycle
    graph.add_use("c", "e");
    graph.add_use("d", "e");
    graph.add_use("e", "c"); // Cycle: c -> e -> c

    assert!(graph.check_cycles().is_err());
}

#[test]
fn circular_topological_order() {
    let mut graph = ImportGraph::new();
    graph.add_use("main", "lib");
    graph.add_use("lib", "utils");
    graph.add_use("main", "utils");

    let order = graph.topological_order();
    assert!(order.is_some());

    let order = order.unwrap();
    // main should be first (no incoming edges)
    assert_eq!(order[0], "main");
}

#[test]
fn circular_topological_order_with_cycle_returns_none() {
    let mut graph = ImportGraph::new();
    graph.add_use("a", "b");
    graph.add_use("b", "a");

    assert!(graph.topological_order().is_none());
}

#[test]
fn circular_transitive_imports() {
    let mut graph = ImportGraph::new();
    graph.add_use("a", "b");
    graph.add_use("b", "c");
    graph.add_use("c", "d");

    let trans = graph.transitive_imports("a");

    assert!(trans.contains("b"));
    assert!(trans.contains("c"));
    assert!(trans.contains("d"));
    assert!(!trans.contains("a")); // Not self
}

// =============================================================================
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
