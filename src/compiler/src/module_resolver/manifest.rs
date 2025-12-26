//! Directory manifest parsing and manipulation.
//!
//! This module handles parsing __init__.spl files and converting them to
//! DirectoryManifest structures, as well as providing methods for working
//! with capabilities and visibility.

use super::types::{ChildModule, DirectoryManifest, ModuleResolver, ResolveResult};
use simple_dependency_tracker::{
    self as tracker,
    macro_import::{AutoImport, MacroDirManifest},
    visibility::{DirManifest as TrackerDirManifest, ModDecl as TrackerModDecl},
};
use simple_parser::ast::{Capability, ImportTarget, Module, Node, Visibility};
use simple_parser::Parser;
use std::path::Path;

use crate::error::CompileError;

impl DirectoryManifest {
    /// Convert to tracker's visibility DirManifest for formal model operations.
    pub fn to_tracker_visibility_manifest(&self) -> TrackerDirManifest {
        let mut manifest = TrackerDirManifest::new(&self.name);
        for child in &self.child_modules {
            manifest.add_child(TrackerModDecl::new(
                &child.name,
                child.visibility == Visibility::Public,
            ));
        }
        // Add exports from export use statements
        for export in &self.exports {
            match &export.target {
                ImportTarget::Single(name) => {
                    manifest.add_export(tracker::visibility::SymbolId::new(name));
                }
                ImportTarget::Aliased { name, .. } => {
                    manifest.add_export(tracker::visibility::SymbolId::new(name));
                }
                ImportTarget::Group(targets) => {
                    for target in targets {
                        if let ImportTarget::Single(name) = target {
                            manifest.add_export(tracker::visibility::SymbolId::new(name));
                        }
                    }
                }
                ImportTarget::Glob => {
                    // Glob exports are handled separately
                }
            }
        }
        manifest
    }

    /// Convert to tracker's macro DirManifest for formal model operations.
    pub fn to_tracker_macro_manifest(&self) -> MacroDirManifest {
        let mut manifest = MacroDirManifest::new(&self.name);
        for auto_import in &self.auto_imports {
            let module_path = auto_import.path.segments.join(".");
            manifest.add_auto_import(AutoImport::new(&module_path, &auto_import.macro_name));
        }
        manifest
    }

    /// Check if a child module is public.
    pub fn is_child_public(&self, name: &str) -> bool {
        self.child_modules
            .iter()
            .any(|c| c.name == name && c.visibility == Visibility::Public)
    }

    /// Check if this manifest's capabilities are a subset of the parent's capabilities.
    /// Returns true if all of this manifest's capabilities are present in the parent.
    /// If parent has no capabilities (empty), child can have any capabilities (unrestricted parent).
    /// If this manifest has no capabilities, it inherits from parent (valid).
    pub fn capabilities_are_subset_of(&self, parent: &[Capability]) -> bool {
        // Empty parent means unrestricted - child can declare anything
        if parent.is_empty() {
            return true;
        }
        // Empty child means it inherits parent's capabilities - always valid
        if self.capabilities.is_empty() {
            return true;
        }
        // Check that all child capabilities are in parent
        self.capabilities.iter().all(|cap| parent.contains(cap))
    }

    /// Compute effective capabilities by intersecting with parent.
    /// If this manifest has no explicit capabilities, inherit from parent.
    /// If both have capabilities, use the intersection.
    pub fn effective_capabilities(&self, parent: &[Capability]) -> Vec<Capability> {
        if self.capabilities.is_empty() {
            // Inherit parent's capabilities
            parent.to_vec()
        } else if parent.is_empty() {
            // Parent is unrestricted, use child's capabilities
            self.capabilities.clone()
        } else {
            // Intersection of child and parent capabilities
            self.capabilities
                .iter()
                .filter(|cap| parent.contains(cap))
                .copied()
                .collect()
        }
    }

    /// Check if a function's effects are allowed by this module's capabilities.
    /// Returns Ok if valid, Err with explanation if invalid.
    /// Effects without corresponding capabilities: Async is always allowed (execution model)
    pub fn validate_function_effects(
        &self,
        func_name: &str,
        effects: &[simple_parser::ast::Effect],
    ) -> Result<(), String> {
        use simple_parser::ast::Effect;

        // If module has no capabilities (unrestricted), all effects are allowed
        if self.capabilities.is_empty() {
            return Ok(());
        }

        for effect in effects {
            match effect {
                // Async is an execution model, not a capability - always allowed
                Effect::Async => {}
                // Pure requires the Pure capability
                Effect::Pure => {
                    if !self.capabilities.contains(&Capability::Pure) {
                        return Err(format!(
                            "function '{}' has @pure effect but module does not allow 'pure' capability",
                            func_name
                        ));
                    }
                }
                // I/O requires the Io capability
                Effect::Io => {
                    if !self.capabilities.contains(&Capability::Io) {
                        return Err(format!(
                            "function '{}' has @io effect but module does not allow 'io' capability",
                            func_name
                        ));
                    }
                }
                // Network requires the Net capability
                Effect::Net => {
                    if !self.capabilities.contains(&Capability::Net) {
                        return Err(format!(
                            "function '{}' has @net effect but module does not allow 'net' capability",
                            func_name
                        ));
                    }
                }
                // Filesystem requires the Fs capability
                Effect::Fs => {
                    if !self.capabilities.contains(&Capability::Fs) {
                        return Err(format!(
                            "function '{}' has @fs effect but module does not allow 'fs' capability",
                            func_name
                        ));
                    }
                }
                // Unsafe requires the Unsafe capability
                Effect::Unsafe => {
                    if !self.capabilities.contains(&Capability::Unsafe) {
                        return Err(format!(
                            "function '{}' has @unsafe effect but module does not allow 'unsafe' capability",
                            func_name
                        ));
                    }
                }
            }
        }

        Ok(())
    }
}

impl ModuleResolver {
    /// Load and parse a directory manifest (__init__.spl)
    pub fn load_manifest(&mut self, dir_path: &Path) -> ResolveResult<DirectoryManifest> {
        let init_path = dir_path.join("__init__.spl");

        if let Some(cached) = self.manifests.get(&init_path) {
            return Ok(cached.clone());
        }

        if !init_path.exists() {
            return Ok(DirectoryManifest::default());
        }

        let source = std::fs::read_to_string(&init_path).map_err(|e| {
            CompileError::Semantic(format!("failed to read {:?}: {}", init_path, e))
        })?;

        let manifest = self.parse_manifest(&source, dir_path)?;
        self.manifests.insert(init_path, manifest.clone());

        Ok(manifest)
    }

    /// Load a manifest and validate its capabilities against parent capabilities.
    ///
    /// This enforces the capability inheritance rule: child modules can only
    /// restrict capabilities, not expand them. A child's capabilities must be
    /// a subset of its parent's capabilities.
    ///
    /// # Arguments
    /// * `dir_path` - Path to the directory containing __init__.spl
    /// * `parent_capabilities` - Capabilities from the parent module (empty = unrestricted)
    ///
    /// # Returns
    /// The loaded manifest, or an error if capabilities are invalid.
    pub fn load_manifest_with_capability_check(
        &mut self,
        dir_path: &Path,
        parent_capabilities: &[Capability],
    ) -> ResolveResult<DirectoryManifest> {
        let manifest = self.load_manifest(dir_path)?;

        // Validate capability inheritance
        if !manifest.capabilities_are_subset_of(parent_capabilities) {
            let child_caps: Vec<&str> = manifest.capabilities.iter().map(|c| c.name()).collect();
            let parent_caps: Vec<&str> = parent_capabilities.iter().map(|c| c.name()).collect();
            return Err(CompileError::Semantic(format!(
                "module '{}' declares capabilities [{}] which are not a subset of parent capabilities [{}]",
                manifest.name,
                child_caps.join(", "),
                parent_caps.join(", ")
            )));
        }

        Ok(manifest)
    }

    /// Parse a directory manifest from source
    pub(super) fn parse_manifest(&self, source: &str, dir_path: &Path) -> ResolveResult<DirectoryManifest> {
        let mut parser = Parser::new(source);
        let module = parser.parse().map_err(|e| {
            CompileError::Semantic(format!("failed to parse __init__.spl: {:?}", e))
        })?;

        self.extract_manifest(&module, dir_path)
    }

    /// Extract manifest information from parsed AST
    pub(super) fn extract_manifest(
        &self,
        module: &Module,
        dir_path: &Path,
    ) -> ResolveResult<DirectoryManifest> {
        let dir_name = dir_path
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown")
            .to_string();

        let mut manifest = DirectoryManifest {
            name: dir_name,
            ..Default::default()
        };

        for item in &module.items {
            match item {
                Node::ModDecl(decl) => {
                    // Check if this is the directory header (mod <dirname>)
                    if manifest.child_modules.is_empty() && decl.name == manifest.name {
                        // This is the directory header - extract attributes
                        manifest.attributes = decl.attributes.clone();
                    } else {
                        // This is a child module declaration
                        manifest.child_modules.push(ChildModule {
                            name: decl.name.clone(),
                            visibility: decl.visibility,
                            attributes: decl.attributes.clone(),
                        });
                    }
                }
                Node::CommonUseStmt(stmt) => {
                    manifest.common_uses.push(stmt.clone());
                }
                Node::ExportUseStmt(stmt) => {
                    manifest.exports.push(stmt.clone());
                }
                Node::AutoImportStmt(stmt) => {
                    manifest.auto_imports.push(stmt.clone());
                }
                Node::RequiresCapabilities(stmt) => {
                    // Extract capabilities from requires [...] statement
                    manifest.capabilities = stmt.capabilities.clone();
                }
                Node::UseStmt(_) => {
                    // Regular use statements in __init__.spl are allowed but
                    // don't affect the manifest structure
                }
                _ => {
                    // Other nodes in __init__.spl are not part of the manifest
                    // (functions, types, etc. should not be in __init__.spl per spec)
                }
            }
        }

        Ok(manifest)
    }
}
