//! # Visibility and Export Model
//!
//! This module implements the visibility and export rules from
//! `verification/visibility_export/src/VisibilityExport.lean`.
//!
//! ## Proven Properties (Lean theorems)
//!
//! 1. `private_stays_private`: A private symbol cannot become public
//! 2. `private_module_restricts`: A symbol in a private module cannot become public
//! 3. `must_be_exported`: A symbol must be explicitly exported to be visible externally
//! 4. `meet_comm`, `meet_assoc`: Visibility meet is commutative and associative
//! 5. `any_private_means_private`: If any ancestor is private, result is private
//! 6. `all_public_means_public`: All public ancestors means public result
//!
//! ## Key Properties
//!
//! 1. Visibility is the **intersection** of declaration visibility and ancestor visibility
//! 2. A directory's public API consists only of:
//!    - Child modules declared as `pub mod` in its `__init__.spl`
//!    - Symbols listed in `export use` inside that same `__init__.spl`
//! 3. Nothing inside a child `.spl` file can make itself "more public" than its directory allows

use std::collections::HashSet;

/// Visibility of a declaration or module.
///
/// Corresponds to Lean: `inductive Visibility | pub | priv`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum Visibility {
    /// Public visibility
    Public,
    /// Private visibility (default)
    #[default]
    Private,
}

impl Visibility {
    /// Check if this visibility is public.
    pub fn is_public(&self) -> bool {
        matches!(self, Visibility::Public)
    }

    /// Check if this visibility is private.
    pub fn is_private(&self) -> bool {
        matches!(self, Visibility::Private)
    }
}

/// A symbol identifier.
///
/// Corresponds to Lean: `structure SymbolId where name : String`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SymbolId {
    pub name: String,
}

impl SymbolId {
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into() }
    }
}

/// A symbol with visibility.
///
/// Corresponds to Lean: `structure Symbol where id : SymbolId; visibility : Visibility`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Symbol {
    pub id: SymbolId,
    pub visibility: Visibility,
}

impl Symbol {
    pub fn new(name: impl Into<String>, visibility: Visibility) -> Self {
        Self {
            id: SymbolId::new(name),
            visibility,
        }
    }

    pub fn public(name: impl Into<String>) -> Self {
        Self::new(name, Visibility::Public)
    }

    pub fn private(name: impl Into<String>) -> Self {
        Self::new(name, Visibility::Private)
    }
}

/// A module declaration in __init__.spl.
///
/// Corresponds to Lean: `structure ModDecl where name : String; isPub : Bool`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModDecl {
    pub name: String,
    pub is_pub: bool,
}

impl ModDecl {
    pub fn new(name: impl Into<String>, is_pub: bool) -> Self {
        Self {
            name: name.into(),
            is_pub,
        }
    }

    pub fn public(name: impl Into<String>) -> Self {
        Self::new(name, true)
    }

    pub fn private(name: impl Into<String>) -> Self {
        Self::new(name, false)
    }
}

/// A directory manifest (__init__.spl).
///
/// Corresponds to Lean: `structure DirManifest where name : String; children : List ModDecl; exports : List SymbolId`
#[derive(Debug, Clone, Default)]
pub struct DirManifest {
    pub name: String,
    pub children: Vec<ModDecl>,
    pub exports: HashSet<SymbolId>,
}

impl DirManifest {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            children: Vec::new(),
            exports: HashSet::new(),
        }
    }

    /// Check if a child module is declared public in the manifest.
    ///
    /// Corresponds to Lean: `def DirManifest.isChildPublic`
    pub fn is_child_public(&self, child_name: &str) -> bool {
        self.children
            .iter()
            .any(|d| d.name == child_name && d.is_pub)
    }

    /// Check if a symbol is explicitly exported.
    ///
    /// Corresponds to Lean: `def DirManifest.isExported`
    pub fn is_exported(&self, sym: &SymbolId) -> bool {
        self.exports.contains(sym)
    }

    /// Add a child module declaration.
    pub fn add_child(&mut self, decl: ModDecl) {
        self.children.push(decl);
    }

    /// Add an export.
    pub fn add_export(&mut self, sym: SymbolId) {
        self.exports.insert(sym);
    }
}

/// Module contents: symbols defined in a module file.
///
/// Corresponds to Lean: `structure ModuleContents where symbols : List Symbol`
#[derive(Debug, Clone, Default)]
pub struct ModuleContents {
    pub symbols: Vec<Symbol>,
}

impl ModuleContents {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a symbol to the module.
    pub fn add_symbol(&mut self, symbol: Symbol) {
        self.symbols.push(symbol);
    }

    /// Get visibility of a symbol from module contents.
    ///
    /// Corresponds to Lean: `def ModuleContents.symbolVisibility`
    pub fn symbol_visibility(&self, sym: &SymbolId) -> Option<Visibility> {
        self.symbols
            .iter()
            .find(|s| s.id == *sym)
            .map(|s| s.visibility)
    }
}

/// Effective visibility result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EffectiveVisibility(pub Visibility);

/// Effective visibility combines declaration visibility with directory control.
///
/// A symbol is externally visible only if:
/// 1. It is declared `pub` in its module
/// 2. Its module is declared `pub mod` in the directory's __init__.spl
/// 3. It's in the export list
///
/// Corresponds to Lean: `def effectiveVisibility`
pub fn effective_visibility(
    manifest: &DirManifest,
    module_name: &str,
    mc: &ModuleContents,
    sym: &SymbolId,
) -> Visibility {
    match mc.symbol_visibility(sym) {
        None => Visibility::Private,                      // Symbol not found
        Some(Visibility::Private) => Visibility::Private, // Declaration is private
        Some(Visibility::Public) => {
            // Symbol is declared public; check if directory allows export
            if manifest.is_child_public(module_name) {
                if manifest.is_exported(sym) {
                    Visibility::Public
                } else {
                    Visibility::Private // Not in export list
                }
            } else {
                Visibility::Private // Module not public
            }
        }
    }
}

/// Alternative: if we include glob exports (export use module.*), check module public.
///
/// Corresponds to Lean: `def effectiveVisibilityWithGlob`
pub fn effective_visibility_with_glob(
    manifest: &DirManifest,
    module_name: &str,
    mc: &ModuleContents,
    sym: &SymbolId,
    has_glob_export: bool,
) -> Visibility {
    match mc.symbol_visibility(sym) {
        None => Visibility::Private,
        Some(Visibility::Private) => Visibility::Private,
        Some(Visibility::Public) => {
            if manifest.is_child_public(module_name) {
                if manifest.is_exported(sym) || has_glob_export {
                    Visibility::Public
                } else {
                    Visibility::Private
                }
            } else {
                Visibility::Private
            }
        }
    }
}

/// Visibility meet operation (intersection).
///
/// Corresponds to Lean: `def visibilityMeet`
///
/// This is the key operation: visibility is the intersection of all visibility levels.
pub fn visibility_meet(v1: Visibility, v2: Visibility) -> Visibility {
    match (v1, v2) {
        (Visibility::Public, Visibility::Public) => Visibility::Public,
        _ => Visibility::Private,
    }
}

/// Ancestor visibility through a path.
///
/// Corresponds to Lean: `def ancestorVisibility (path : List Visibility) : Visibility`
///
/// This computes the effective visibility by folding visibility_meet over the path.
pub fn ancestor_visibility(path: &[Visibility]) -> Visibility {
    path.iter()
        .fold(Visibility::Public, |acc, &v| visibility_meet(acc, v))
}

#[cfg(test)]
mod tests {
    use super::*;

    // Theorem: private_stays_private
    // A private symbol cannot become public regardless of directory settings.
    #[test]
    fn theorem_private_stays_private() {
        let manifest = DirManifest::new("test");
        let mut mc = ModuleContents::new();
        mc.add_symbol(Symbol::private("foo"));
        let sym = SymbolId::new("foo");

        assert_eq!(
            effective_visibility(&manifest, "any_module", &mc, &sym),
            Visibility::Private
        );
    }

    // Theorem: private_module_restricts
    // A symbol in a private module cannot become public.
    #[test]
    fn theorem_private_module_restricts() {
        let mut manifest = DirManifest::new("test");
        manifest.add_child(ModDecl::private("mymodule"));
        manifest.add_export(SymbolId::new("foo"));

        let mut mc = ModuleContents::new();
        mc.add_symbol(Symbol::public("foo"));
        let sym = SymbolId::new("foo");

        assert_eq!(
            effective_visibility(&manifest, "mymodule", &mc, &sym),
            Visibility::Private
        );
    }

    // Theorem: must_be_exported
    // A symbol must be explicitly exported to be visible externally.
    #[test]
    fn theorem_must_be_exported() {
        let mut manifest = DirManifest::new("test");
        manifest.add_child(ModDecl::public("mymodule"));
        // Note: NOT adding export for "foo"

        let mut mc = ModuleContents::new();
        mc.add_symbol(Symbol::public("foo"));
        let sym = SymbolId::new("foo");

        // Even though module is public and symbol is public, it's not exported
        assert_eq!(
            effective_visibility(&manifest, "mymodule", &mc, &sym),
            Visibility::Private
        );
    }

    #[test]
    fn fully_public_symbol() {
        let mut manifest = DirManifest::new("test");
        manifest.add_child(ModDecl::public("mymodule"));
        manifest.add_export(SymbolId::new("foo"));

        let mut mc = ModuleContents::new();
        mc.add_symbol(Symbol::public("foo"));
        let sym = SymbolId::new("foo");

        assert_eq!(
            effective_visibility(&manifest, "mymodule", &mc, &sym),
            Visibility::Public
        );
    }

    // Theorem: meet_comm
    // Visibility meet is commutative.
    #[test]
    fn theorem_meet_comm() {
        for v1 in [Visibility::Public, Visibility::Private] {
            for v2 in [Visibility::Public, Visibility::Private] {
                assert_eq!(visibility_meet(v1, v2), visibility_meet(v2, v1));
            }
        }
    }

    // Theorem: meet_assoc
    // Visibility meet is associative.
    #[test]
    fn theorem_meet_assoc() {
        for v1 in [Visibility::Public, Visibility::Private] {
            for v2 in [Visibility::Public, Visibility::Private] {
                for v3 in [Visibility::Public, Visibility::Private] {
                    assert_eq!(
                        visibility_meet(visibility_meet(v1, v2), v3),
                        visibility_meet(v1, visibility_meet(v2, v3))
                    );
                }
            }
        }
    }

    // Theorem: any_private_means_private
    // If any ancestor is private, result is private.
    #[test]
    fn theorem_any_private_means_private() {
        let path = vec![Visibility::Public, Visibility::Private, Visibility::Public];
        assert_eq!(ancestor_visibility(&path), Visibility::Private);
    }

    // Theorem: all_public_means_public
    // All public ancestors means public result.
    #[test]
    fn theorem_all_public_means_public() {
        let path = vec![Visibility::Public, Visibility::Public, Visibility::Public];
        assert_eq!(ancestor_visibility(&path), Visibility::Public);
    }

    #[test]
    fn empty_path_is_public() {
        assert_eq!(ancestor_visibility(&[]), Visibility::Public);
    }

    #[test]
    fn meet_private_absorbs() {
        assert_eq!(
            visibility_meet(Visibility::Private, Visibility::Public),
            Visibility::Private
        );
        assert_eq!(
            visibility_meet(Visibility::Public, Visibility::Private),
            Visibility::Private
        );
    }

    #[test]
    fn meet_public_identity() {
        assert_eq!(
            visibility_meet(Visibility::Public, Visibility::Public),
            Visibility::Public
        );
    }
}
