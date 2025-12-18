// DirectoryManifest implementation - methods for visibility, capabilities, and effect validation

use super::*;

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
