//! Package manager CLI commands

pub mod add;
pub mod cache_cmd;
pub mod init;
pub mod install;
pub mod list;
pub mod update;

pub use add::{add_dependency, remove_dependency};
pub use cache_cmd::{cache_clean, cache_info, cache_list, format_size};
pub use init::init_project;
pub use install::install_dependencies;
pub use list::{dependency_tree, format_tree, list_dependencies};
pub use update::{update_all, update_package};

#[cfg(test)]
pub mod test_helpers {
    use crate::commands::init::init_project;
    use std::fs;
    use std::path::PathBuf;

    /// Create a temporary test project directory with a unique name.
    /// The caller is responsible for cleaning up the directory.
    pub fn setup_test_project(prefix: &str, name: &str) -> PathBuf {
        let temp_dir = std::env::temp_dir().join(format!(
            "simple-{}-test-{}-{}",
            prefix,
            name,
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let _ = fs::remove_dir_all(&temp_dir);
        fs::create_dir_all(&temp_dir).unwrap();
        init_project(&temp_dir, Some(name)).unwrap();
        temp_dir
    }

    /// Clean up a test project directory
    pub fn cleanup_test_project(dir: &PathBuf) {
        let _ = fs::remove_dir_all(dir);
    }

    /// Setup a transitive dependency chain: main -> lib_a -> lib_b
    /// Returns (temp_dir, lib_a_path, lib_b_path)
    pub fn setup_transitive_deps(prefix: &str, name: &str) -> (PathBuf, PathBuf, PathBuf) {
        use crate::manifest::{Dependency, Manifest};

        let temp_dir = setup_test_project(prefix, name);

        // Create lib_b (no deps)
        let lib_b = temp_dir.join("lib_b");
        fs::create_dir_all(&lib_b).unwrap();
        init_project(&lib_b, Some("lib_b")).unwrap();

        // Create lib_a (depends on lib_b)
        let lib_a = temp_dir.join("lib_a");
        fs::create_dir_all(&lib_a).unwrap();
        init_project(&lib_a, Some("lib_a")).unwrap();
        let mut lib_a_manifest = Manifest::load(&lib_a.join("simple.toml")).unwrap();
        lib_a_manifest.add_dependency("lib_b", Dependency::path("../lib_b"));
        lib_a_manifest.save(&lib_a.join("simple.toml")).unwrap();

        // Main project depends on lib_a
        let mut manifest = Manifest::load(&temp_dir.join("simple.toml")).unwrap();
        manifest.add_dependency("lib_a", Dependency::path("./lib_a"));
        manifest.save(&temp_dir.join("simple.toml")).unwrap();

        (temp_dir, lib_a, lib_b)
    }
}
