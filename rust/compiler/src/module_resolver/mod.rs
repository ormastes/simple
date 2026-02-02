//! Module resolver for the Simple language module system.
//!
//! This module handles resolving module paths to filesystem locations
//! and managing directory manifests (__init__.spl files).
//!
//! ## Integration with dependency_tracker
//!
//! This module bridges the parser's AST types with the formally-verified
//! types in `simple_dependency_tracker`. The formal models ensure:
//!
//! - Module resolution is unambiguous (no foo.spl + foo/__init__.spl conflicts)
//! - Visibility is the intersection of item and ancestor visibility
//! - Glob imports only include macros listed in `auto import`

mod manifest;
mod resolution;
mod types;

// Re-export public types
pub use types::{ChildModule, DirectoryManifest, ModuleResolver, ResolveResult, ResolvedModule};

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_helpers::create_test_project;
    use simple_dependency_tracker::{
        macro_import::{MacroExports, MacroSymbol, SymKind},
        visibility::Visibility as TrackerVisibility,
    };
    use simple_parser::ast::{Capability, ModulePath, Visibility};
    use std::fs;
    use std::path::Path;

    #[test]
    fn test_resolver_creation() {
        let dir = create_test_project();
        let resolver = ModuleResolver::new(dir.path().to_path_buf(), dir.path().join("src"));
        assert_eq!(resolver.project_root(), dir.path());
        assert_eq!(resolver.source_root(), dir.path().join("src"));
    }

    #[test]
    fn test_single_file_mode() {
        let resolver = ModuleResolver::single_file(Path::new("/tmp/test.spl"));
        assert_eq!(resolver.project_root(), Path::new("/tmp"));
        assert_eq!(resolver.source_root(), Path::new("/tmp"));
    }

    #[test]
    fn test_resolve_file_module() {
        let dir = create_test_project();
        let src = dir.path().join("src");

        // Create a module file
        fs::write(src.join("utils.spl"), "fn helper(): 42").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["crate".into(), "utils".into()]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();

        assert_eq!(resolved.path, src.join("utils.spl"));
        assert!(!resolved.is_directory);
    }

    #[test]
    fn test_resolve_directory_module() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let http = src.join("http");
        fs::create_dir_all(&http).unwrap();

        // Create __init__.spl
        fs::write(http.join("__init__.spl"), "mod http\npub mod router").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["crate".into(), "http".into()]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();

        assert_eq!(resolved.path, http.join("__init__.spl"));
        assert!(resolved.is_directory);
    }

    #[test]
    fn test_resolve_nested_module() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let http = src.join("sys").join("http");
        fs::create_dir_all(&http).unwrap();

        fs::write(http.join("router.spl"), "struct Router:").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["crate".into(), "sys".into(), "http".into(), "router".into()]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();

        assert_eq!(resolved.path, http.join("router.spl"));
    }

    #[test]
    fn test_resolve_module_not_found() {
        let dir = create_test_project();
        let src = dir.path().join("src");

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["crate".into(), "nonexistent".into()]);
        let result = resolver.resolve(&path, &src.join("main.spl"));

        assert!(result.is_err());
    }

    #[test]
    fn test_parse_manifest() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let http = src.join("http");
        fs::create_dir_all(&http).unwrap();

        let manifest_source = r#"
#[no_gc]
mod http

pub mod router
mod internal

common use crate.core.base.*

export use router.Router
export use router.route

auto import router.route
"#;
        fs::write(http.join("__init__.spl"), manifest_source).unwrap();

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);

        let manifest = resolver.load_manifest(&http).unwrap();

        assert_eq!(manifest.name, "http");
        assert_eq!(manifest.child_modules.len(), 2);
        assert_eq!(manifest.child_modules[0].name, "router");
        assert_eq!(manifest.child_modules[0].visibility, Visibility::Public);
        assert_eq!(manifest.child_modules[1].name, "internal");
        assert_eq!(manifest.child_modules[1].visibility, Visibility::Private);
        assert_eq!(manifest.common_uses.len(), 1);
        assert_eq!(manifest.exports.len(), 2);
        assert_eq!(manifest.auto_imports.len(), 1);
    }

    #[test]
    fn test_features() {
        let dir = create_test_project();
        let mut features = std::collections::HashSet::new();
        features.insert("strict_null".into());

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), dir.path().join("src")).with_features(features);

        assert!(resolver.is_feature_enabled("strict_null"));
        assert!(!resolver.is_feature_enabled("other_feature"));
    }

    #[test]
    fn test_effective_visibility_formal_model() {
        // This test demonstrates the integration with the formal verification model
        // from verification/visibility_export/
        let dir = create_test_project();
        let src = dir.path().join("src");
        let http = src.join("http");
        fs::create_dir_all(&http).unwrap();

        let manifest_source = r#"
mod http
pub mod router
mod internal
export use router.Router
"#;
        fs::write(http.join("__init__.spl"), manifest_source).unwrap();

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);

        let manifest = resolver.load_manifest(&http).unwrap();

        // Public module + exported symbol = public effective visibility
        let vis = resolver.effective_visibility(&manifest, "router", "Router", Visibility::Public);
        assert_eq!(vis, TrackerVisibility::Public);

        // Public module + unexported symbol = private effective visibility
        let vis = resolver.effective_visibility(&manifest, "router", "helper", Visibility::Public);
        assert_eq!(vis, TrackerVisibility::Private);

        // Private module = private effective visibility
        let vis = resolver.effective_visibility(&manifest, "internal", "Foo", Visibility::Public);
        assert_eq!(vis, TrackerVisibility::Private);

        // Private symbol = private effective visibility
        let vis = resolver.effective_visibility(&manifest, "router", "Router", Visibility::Private);
        assert_eq!(vis, TrackerVisibility::Private);
    }

    #[test]
    fn test_macro_auto_import_formal_model() {
        // This test demonstrates the integration with the formal verification model
        // from verification/macro_auto_import/
        let dir = create_test_project();
        let src = dir.path().join("src");
        let http = src.join("http");
        fs::create_dir_all(&http).unwrap();

        let manifest_source = r#"
mod http
pub mod router
auto import router.route
"#;
        fs::write(http.join("__init__.spl"), manifest_source).unwrap();

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);

        let manifest = resolver.load_manifest(&http).unwrap();

        // Create mock exports
        let mut exports = MacroExports::new();
        exports.add_non_macro(MacroSymbol::value("router", "Router"));
        exports.add_macro(MacroSymbol::macro_def("router", "route"));
        exports.add_macro(MacroSymbol::macro_def("router", "get"));

        // Glob import should include:
        // - All non-macros (Router)
        // - Only auto-imported macros (route, not get)
        let result = resolver.filter_glob_import(&manifest, &exports);

        assert_eq!(result.len(), 2); // Router + route
        assert!(result
            .iter()
            .any(|s| s.name == "Router" && s.kind == SymKind::ValueOrType));
        assert!(result.iter().any(|s| s.name == "route" && s.kind == SymKind::Macro));
        assert!(!result.iter().any(|s| s.name == "get")); // Not in auto import
    }

    #[test]
    fn test_circular_dependency_detection() {
        use simple_dependency_tracker::graph::ImportKind;

        let dir = create_test_project();
        let src = dir.path().join("src");

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);

        // Create a cycle: a -> b -> c -> a
        resolver.record_import("crate.a", "crate.b", ImportKind::Use);
        resolver.record_import("crate.b", "crate.c", ImportKind::Use);
        resolver.record_import("crate.c", "crate.a", ImportKind::Use);

        let result = resolver.check_circular_dependencies();
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("Circular dependency"));
    }

    // ========================================================================
    // Capability Inheritance Tests
    // ========================================================================

    #[test]
    fn test_capabilities_subset_unrestricted_parent() {
        // Empty parent means unrestricted - child can declare anything
        let manifest = DirectoryManifest {
            capabilities: vec![Capability::Pure, Capability::Io],
            ..Default::default()
        };
        let parent: Vec<Capability> = vec![];

        assert!(manifest.capabilities_are_subset_of(&parent));
    }

    #[test]
    fn test_capabilities_subset_inherit_from_parent() {
        // Empty child inherits from parent - always valid
        let manifest = DirectoryManifest {
            capabilities: vec![],
            ..Default::default()
        };
        let parent = vec![Capability::Pure, Capability::Io];

        assert!(manifest.capabilities_are_subset_of(&parent));
    }

    #[test]
    fn test_capabilities_subset_valid_restriction() {
        // Child restricts to subset of parent - valid
        let manifest = DirectoryManifest {
            capabilities: vec![Capability::Pure],
            ..Default::default()
        };
        let parent = vec![Capability::Pure, Capability::Io, Capability::Net];

        assert!(manifest.capabilities_are_subset_of(&parent));
    }

    #[test]
    fn test_capabilities_subset_invalid_expansion() {
        // Child tries to add capability not in parent - invalid
        let manifest = DirectoryManifest {
            capabilities: vec![Capability::Pure, Capability::Net],
            ..Default::default()
        };
        let parent = vec![Capability::Pure, Capability::Io];

        assert!(!manifest.capabilities_are_subset_of(&parent));
    }

    #[test]
    fn test_effective_capabilities_inherit() {
        // Empty child inherits parent's capabilities
        let manifest = DirectoryManifest {
            capabilities: vec![],
            ..Default::default()
        };
        let parent = vec![Capability::Pure, Capability::Io];

        let effective = manifest.effective_capabilities(&parent);
        assert_eq!(effective, parent);
    }

    #[test]
    fn test_effective_capabilities_unrestricted_parent() {
        // Unrestricted parent - child's capabilities become effective
        let manifest = DirectoryManifest {
            capabilities: vec![Capability::Pure],
            ..Default::default()
        };
        let parent: Vec<Capability> = vec![];

        let effective = manifest.effective_capabilities(&parent);
        assert_eq!(effective, vec![Capability::Pure]);
    }

    #[test]
    fn test_effective_capabilities_intersection() {
        // Intersection of child and parent
        let manifest = DirectoryManifest {
            capabilities: vec![Capability::Pure, Capability::Io, Capability::Net],
            ..Default::default()
        };
        let parent = vec![Capability::Pure, Capability::Io, Capability::Fs];

        let effective = manifest.effective_capabilities(&parent);
        assert_eq!(effective.len(), 2);
        assert!(effective.contains(&Capability::Pure));
        assert!(effective.contains(&Capability::Io));
    }

    #[test]
    fn test_validate_effects_unrestricted() {
        use simple_parser::ast::Effect;

        // Unrestricted module allows all effects
        let manifest = DirectoryManifest {
            capabilities: vec![],
            ..Default::default()
        };

        assert!(manifest
            .validate_function_effects("test", &[Effect::Pure, Effect::Io, Effect::Net])
            .is_ok());
    }

    #[test]
    fn test_validate_effects_allowed() {
        use simple_parser::ast::Effect;

        // Module allows matching effects
        let manifest = DirectoryManifest {
            capabilities: vec![Capability::Pure, Capability::Io],
            ..Default::default()
        };

        assert!(manifest.validate_function_effects("test", &[Effect::Pure]).is_ok());
        assert!(manifest.validate_function_effects("test", &[Effect::Io]).is_ok());
        assert!(manifest
            .validate_function_effects("test", &[Effect::Pure, Effect::Io])
            .is_ok());
    }

    #[test]
    fn test_validate_effects_blocked() {
        use simple_parser::ast::Effect;

        // Module blocks effects not in capabilities
        let manifest = DirectoryManifest {
            capabilities: vec![Capability::Pure],
            ..Default::default()
        };

        // @io is not allowed
        let result = manifest.validate_function_effects("test", &[Effect::Io]);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("'io' capability"));

        // @net is not allowed
        let result = manifest.validate_function_effects("test", &[Effect::Net]);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("'net' capability"));
    }

    #[test]
    fn test_validate_effects_async_always_allowed() {
        use simple_parser::ast::Effect;

        // @async is always allowed (execution model, not capability)
        let manifest = DirectoryManifest {
            capabilities: vec![Capability::Pure],
            ..Default::default()
        };

        assert!(manifest.validate_function_effects("test", &[Effect::Async]).is_ok());
        assert!(manifest
            .validate_function_effects("test", &[Effect::Pure, Effect::Async])
            .is_ok());
    }

    // ========================================================================
    // Module Load with Capability Check Tests
    // ========================================================================

    #[test]
    fn test_load_manifest_with_capability_check_unrestricted_parent() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let child = src.join("child");
        fs::create_dir_all(&child).unwrap();

        // Child module with [pure, io] capabilities
        fs::write(child.join("__init__.spl"), "mod child\nrequires [pure, io]").unwrap();

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);

        // Unrestricted parent (empty) - child can declare anything
        let parent_caps: Vec<Capability> = vec![];
        let manifest = resolver
            .load_manifest_with_capability_check(&child, &parent_caps)
            .unwrap();

        assert_eq!(manifest.capabilities.len(), 2);
        assert!(manifest.capabilities.contains(&Capability::Pure));
        assert!(manifest.capabilities.contains(&Capability::Io));
    }

    #[test]
    fn test_load_manifest_with_capability_check_valid_subset() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let child = src.join("child");
        fs::create_dir_all(&child).unwrap();

        // Child restricts to [pure] which is a subset of parent's [pure, io]
        fs::write(child.join("__init__.spl"), "mod child\nrequires [pure]").unwrap();

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);

        let parent_caps = vec![Capability::Pure, Capability::Io];
        let manifest = resolver
            .load_manifest_with_capability_check(&child, &parent_caps)
            .unwrap();

        assert_eq!(manifest.capabilities, vec![Capability::Pure]);
    }

    #[test]
    fn test_load_manifest_with_capability_check_invalid_expansion() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let child = src.join("child");
        fs::create_dir_all(&child).unwrap();

        // Child tries [pure, net] but parent only allows [pure, io]
        fs::write(child.join("__init__.spl"), "mod child\nrequires [pure, net]").unwrap();

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);

        let parent_caps = vec![Capability::Pure, Capability::Io];
        let result = resolver.load_manifest_with_capability_check(&child, &parent_caps);

        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("not a subset"));
        assert!(err_msg.contains("pure, net"));
        assert!(err_msg.contains("pure, io"));
    }

    #[test]
    fn test_load_manifest_with_capability_check_empty_child() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let child = src.join("child");
        fs::create_dir_all(&child).unwrap();

        // Child has no requires statement - inherits from parent
        fs::write(child.join("__init__.spl"), "mod child").unwrap();

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);

        let parent_caps = vec![Capability::Pure, Capability::Io];
        let manifest = resolver
            .load_manifest_with_capability_check(&child, &parent_caps)
            .unwrap();

        // Child inherits parent capabilities (empty means inherit)
        assert!(manifest.capabilities.is_empty());
        // Effective capabilities would be parent's
        let effective = manifest.effective_capabilities(&parent_caps);
        assert_eq!(effective, parent_caps);
    }

    #[test]
    fn test_load_manifest_with_capability_check_no_manifest() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let child = src.join("child");
        fs::create_dir_all(&child).unwrap();
        // No __init__.spl - directory without manifest

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);

        let parent_caps = vec![Capability::Pure];
        let manifest = resolver
            .load_manifest_with_capability_check(&child, &parent_caps)
            .unwrap();

        // Empty manifest with no capabilities (inherits parent)
        assert!(manifest.capabilities.is_empty());
    }

    // =========================================================================
    // is_bypass field tests
    // =========================================================================

    #[test]
    fn test_manifest_is_bypass_default_false() {
        let manifest = DirectoryManifest::default();
        assert!(!manifest.is_bypass, "default manifest should not be bypass");
    }

    #[test]
    fn test_manifest_bypass_parsed_from_init() {
        use std::fs;

        let dir = tempfile::TempDir::new().unwrap();
        let src = dir.path().join("src");
        let lib = src.join("lib");
        fs::create_dir_all(&lib).unwrap();

        // __init__.spl with #[bypass] on the directory header mod
        fs::write(lib.join("__init__.spl"), "#[bypass]\nmod lib\n").unwrap();

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);
        let manifest = resolver.load_manifest(&lib).unwrap();

        assert!(manifest.is_bypass, "manifest should have is_bypass = true");
    }

    #[test]
    fn test_manifest_no_bypass_without_attribute() {
        use std::fs;

        let dir = tempfile::TempDir::new().unwrap();
        let src = dir.path().join("src");
        let pkg = src.join("pkg");
        fs::create_dir_all(&pkg).unwrap();

        fs::write(
            pkg.join("__init__.spl"),
            "mod pkg\npub mod router\nexport use router.Router\n",
        )
        .unwrap();

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);
        let manifest = resolver.load_manifest(&pkg).unwrap();

        assert!(!manifest.is_bypass, "manifest without #[bypass] should not be bypass");
    }

    #[test]
    fn test_manifest_bypass_with_child_modules() {
        use std::fs;

        let dir = tempfile::TempDir::new().unwrap();
        let src = dir.path().join("src");
        let lib = src.join("lib");
        fs::create_dir_all(&lib).unwrap();

        // bypass directory with child modules declared
        fs::write(
            lib.join("__init__.spl"),
            "#[bypass]\nmod lib\npub mod http\npub mod db\n",
        )
        .unwrap();

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);
        let manifest = resolver.load_manifest(&lib).unwrap();

        assert!(manifest.is_bypass);
        assert_eq!(manifest.child_modules.len(), 2);
        assert_eq!(manifest.child_modules[0].name, "http");
        assert_eq!(manifest.child_modules[1].name, "db");
    }
}
