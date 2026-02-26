//! # Macro Auto-Import Model
//!
//! This module implements the macro import/export and `auto import` semantics from
//! `verification/macro_auto_import/src/MacroAutoImport.lean`.
//!
//! ## Proven Properties (Lean theorems)
//!
//! 1. `glob_doesnt_leak_macros_wf`: Macros not in auto-import are never in glob import result
//! 2. `nonmacros_always_globbed`: All non-macros are always in glob import
//! 3. `auto_imported_in_glob`: Auto-imported macros are in glob import
//! 4. `glob_subset`: Glob import symbols come from exports
//! 5. `empty_auto_import_no_macros`: Empty auto-import means no macros in glob
//! 6. `autoImported_combine`: Combined exports combine auto-imported macros
//!
//! ## Key Properties (Invariants)
//!
//! 1. **Glob doesn't leak**: If macro `m` is not in `auto import`, then `m` is never
//!    in the result of `globImport`
//! 2. **Explicit always works**: Explicit `use module.macroName` always imports the macro
//!    if it exists and is public
//! 3. **Two-phase visibility**: Macro export happens in Phase 1 (module exports it),
//!    glob participation happens in Phase 2 (directory's `autoImports` lists it)

use std::collections::HashSet;

/// Symbol kind distinguishes macros from other symbols.
///
/// Corresponds to Lean: `inductive SymKind | valueOrType | macro`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SymKind {
    /// Functions, types, constants
    ValueOrType,
    /// Macro definitions
    Macro,
}

impl SymKind {
    pub fn is_macro(&self) -> bool {
        matches!(self, SymKind::Macro)
    }
}

/// A fully-qualified symbol.
///
/// Corresponds to Lean: `structure Symbol where modulePath : String; name : String; kind : SymKind`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MacroSymbol {
    pub module_path: String,
    pub name: String,
    pub kind: SymKind,
}

impl MacroSymbol {
    pub fn new(module_path: impl Into<String>, name: impl Into<String>, kind: SymKind) -> Self {
        Self {
            module_path: module_path.into(),
            name: name.into(),
            kind,
        }
    }

    pub fn value(module_path: impl Into<String>, name: impl Into<String>) -> Self {
        Self::new(module_path, name, SymKind::ValueOrType)
    }

    pub fn macro_def(module_path: impl Into<String>, name: impl Into<String>) -> Self {
        Self::new(module_path, name, SymKind::Macro)
    }
}

/// Auto-import declaration from __init__.spl.
///
/// Corresponds to Lean: `structure AutoImport where fromModule : String; macroName : String`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AutoImport {
    pub from_module: String,
    pub macro_name: String,
}

impl AutoImport {
    pub fn new(from_module: impl Into<String>, macro_name: impl Into<String>) -> Self {
        Self {
            from_module: from_module.into(),
            macro_name: macro_name.into(),
        }
    }
}

/// What a module publicly exports.
///
/// Corresponds to Lean: `structure ModuleExports where nonMacros : List Symbol; macros : List Symbol`
#[derive(Debug, Clone, Default)]
pub struct MacroExports {
    /// Public non-macro symbols
    pub non_macros: Vec<MacroSymbol>,
    /// Public macros
    pub macros: Vec<MacroSymbol>,
}

impl MacroExports {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a non-macro symbol.
    pub fn add_non_macro(&mut self, sym: MacroSymbol) {
        debug_assert!(sym.kind == SymKind::ValueOrType);
        self.non_macros.push(sym);
    }

    /// Add a macro symbol.
    pub fn add_macro(&mut self, sym: MacroSymbol) {
        debug_assert!(sym.kind == SymKind::Macro);
        self.macros.push(sym);
    }

    /// Add a symbol (automatically categorized).
    pub fn add(&mut self, sym: MacroSymbol) {
        match sym.kind {
            SymKind::ValueOrType => self.non_macros.push(sym),
            SymKind::Macro => self.macros.push(sym),
        }
    }

    /// Check well-formedness: nonMacros contains only non-macros, macros contains only macros.
    ///
    /// Corresponds to Lean: `def wellFormedExports`
    pub fn is_well_formed(&self) -> bool {
        self.non_macros.iter().all(|s| s.kind == SymKind::ValueOrType)
            && self.macros.iter().all(|s| s.kind == SymKind::Macro)
    }
}

/// Directory manifest for macro handling.
///
/// Corresponds to Lean: `structure DirManifest where name : String; autoImports : List AutoImport`
#[derive(Debug, Clone, Default)]
pub struct MacroDirManifest {
    pub name: String,
    pub auto_imports: HashSet<AutoImport>,
}

impl MacroDirManifest {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            auto_imports: HashSet::new(),
        }
    }

    /// Add an auto-import declaration.
    pub fn add_auto_import(&mut self, ai: AutoImport) {
        self.auto_imports.insert(ai);
    }
}

/// Check if a macro is in the auto-import list.
///
/// Corresponds to Lean: `def isAutoImported (m : DirManifest) (sym : Symbol) : Bool`
pub fn is_auto_imported(manifest: &MacroDirManifest, sym: &MacroSymbol) -> bool {
    sym.kind == SymKind::Macro
        && manifest
            .auto_imports
            .iter()
            .any(|ai| ai.from_module == sym.module_path && ai.macro_name == sym.name)
}

/// Filter macros that are in auto-import list.
///
/// Corresponds to Lean: `def autoImportedMacros (m : DirManifest) (exports : ModuleExports) : List Symbol`
pub fn auto_imported_macros(manifest: &MacroDirManifest, exports: &MacroExports) -> Vec<MacroSymbol> {
    exports
        .macros
        .iter()
        .filter(|sym| is_auto_imported(manifest, sym))
        .cloned()
        .collect()
}

/// Glob import result: non-macros + auto-imported macros only.
///
/// Corresponds to Lean: `def globImport (m : DirManifest) (exports : ModuleExports) : List Symbol`
///
/// This is the key function: it returns all non-macros, plus ONLY the macros
/// that are listed in `auto import`.
pub fn glob_import(manifest: &MacroDirManifest, exports: &MacroExports) -> Vec<MacroSymbol> {
    let mut result = exports.non_macros.clone();
    result.extend(auto_imported_macros(manifest, exports));
    result
}

/// Explicit import: always works for any public symbol.
///
/// Corresponds to Lean: `def explicitImport (exports : ModuleExports) (name : String) : Option Symbol`
pub fn explicit_import(exports: &MacroExports, name: &str) -> Option<MacroSymbol> {
    exports
        .non_macros
        .iter()
        .chain(exports.macros.iter())
        .find(|s| s.name == name)
        .cloned()
}

/// Combine two module exports.
///
/// Corresponds to Lean: `def combineExports (e1 e2 : ModuleExports) : ModuleExports`
pub fn combine_exports(e1: &MacroExports, e2: &MacroExports) -> MacroExports {
    let mut result = MacroExports::new();
    result.non_macros.extend(e1.non_macros.iter().cloned());
    result.non_macros.extend(e2.non_macros.iter().cloned());
    result.macros.extend(e1.macros.iter().cloned());
    result.macros.extend(e2.macros.iter().cloned());
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_exports() -> MacroExports {
        let mut exports = MacroExports::new();
        exports.add_non_macro(MacroSymbol::value("mod", "foo"));
        exports.add_non_macro(MacroSymbol::value("mod", "bar"));
        exports.add_macro(MacroSymbol::macro_def("mod", "my_macro"));
        exports.add_macro(MacroSymbol::macro_def("mod", "other_macro"));
        exports
    }

    // Theorem: glob_doesnt_leak_macros_wf
    // Macros not in auto-import are never in glob import result (well-formed exports).
    #[test]
    fn theorem_glob_doesnt_leak_macros() {
        let exports = make_exports();
        assert!(exports.is_well_formed());

        // Manifest with only "my_macro" in auto-import
        let mut manifest = MacroDirManifest::new("test");
        manifest.add_auto_import(AutoImport::new("mod", "my_macro"));

        let result = glob_import(&manifest, &exports);

        // "other_macro" should NOT be in the result
        assert!(!result.iter().any(|s| s.name == "other_macro"));

        // "my_macro" SHOULD be in the result
        assert!(result.iter().any(|s| s.name == "my_macro"));
    }

    // Theorem: nonmacros_always_globbed
    // All non-macros are always in glob import.
    #[test]
    fn theorem_nonmacros_always_globbed() {
        let exports = make_exports();
        let manifest = MacroDirManifest::new("test"); // Empty auto-imports

        let result = glob_import(&manifest, &exports);

        // All non-macros should be present
        assert!(result.iter().any(|s| s.name == "foo"));
        assert!(result.iter().any(|s| s.name == "bar"));
    }

    // Theorem: auto_imported_in_glob
    // Auto-imported macros are in glob import.
    #[test]
    fn theorem_auto_imported_in_glob() {
        let exports = make_exports();
        let mut manifest = MacroDirManifest::new("test");
        manifest.add_auto_import(AutoImport::new("mod", "my_macro"));

        let result = glob_import(&manifest, &exports);

        assert!(result.iter().any(|s| s.name == "my_macro" && s.kind == SymKind::Macro));
    }

    // Theorem: glob_subset
    // Glob import result symbols come from exports.
    #[test]
    fn theorem_glob_subset() {
        let exports = make_exports();
        let mut manifest = MacroDirManifest::new("test");
        manifest.add_auto_import(AutoImport::new("mod", "my_macro"));

        let result = glob_import(&manifest, &exports);

        // Every symbol in result is either in non_macros or macros
        for sym in &result {
            let in_non_macros = exports.non_macros.contains(sym);
            let in_macros = exports.macros.contains(sym);
            assert!(in_non_macros || in_macros);
        }
    }

    // Theorem: empty_auto_import_no_macros
    // Empty auto-import means no macros in glob result.
    #[test]
    fn theorem_empty_auto_import_no_macros() {
        let exports = make_exports();
        let manifest = MacroDirManifest::new("test"); // Empty

        let auto_macros = auto_imported_macros(&manifest, &exports);
        assert!(auto_macros.is_empty());

        let result = glob_import(&manifest, &exports);
        // Only non-macros in result
        for sym in &result {
            assert_eq!(sym.kind, SymKind::ValueOrType);
        }
    }

    // Theorem: autoImported_combine
    // AutoImported macros from combined exports is the combination.
    #[test]
    fn theorem_auto_imported_combine() {
        let mut e1 = MacroExports::new();
        e1.add_macro(MacroSymbol::macro_def("mod1", "macro1"));

        let mut e2 = MacroExports::new();
        e2.add_macro(MacroSymbol::macro_def("mod2", "macro2"));

        let combined = combine_exports(&e1, &e2);

        let mut manifest = MacroDirManifest::new("test");
        manifest.add_auto_import(AutoImport::new("mod1", "macro1"));
        manifest.add_auto_import(AutoImport::new("mod2", "macro2"));

        let auto1 = auto_imported_macros(&manifest, &e1);
        let auto2 = auto_imported_macros(&manifest, &e2);
        let auto_combined = auto_imported_macros(&manifest, &combined);

        // Combined auto-imports equals sum of individual auto-imports
        assert_eq!(auto_combined.len(), auto1.len() + auto2.len());
    }

    // Explicit import always works for any public symbol
    #[test]
    fn explicit_import_finds_non_macro() {
        let exports = make_exports();
        let result = explicit_import(&exports, "foo");
        assert!(result.is_some());
        assert_eq!(result.unwrap().name, "foo");
    }

    #[test]
    fn explicit_import_finds_macro() {
        let exports = make_exports();
        let result = explicit_import(&exports, "my_macro");
        assert!(result.is_some());
        let sym = result.unwrap();
        assert_eq!(sym.name, "my_macro");
        assert_eq!(sym.kind, SymKind::Macro);
    }

    #[test]
    fn explicit_import_not_found() {
        let exports = make_exports();
        let result = explicit_import(&exports, "nonexistent");
        assert!(result.is_none());
    }

    #[test]
    fn is_auto_imported_checks_kind() {
        let manifest = MacroDirManifest::new("test");
        // Even if the name matches, a non-macro is not auto-imported
        let non_macro = MacroSymbol::value("mod", "foo");
        assert!(!is_auto_imported(&manifest, &non_macro));
    }
}
