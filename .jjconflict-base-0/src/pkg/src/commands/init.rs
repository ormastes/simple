//! `simple init` command - Create a new Simple project

use std::path::Path;

use crate::error::{PkgError, PkgResult};
use crate::manifest::Manifest;

/// Initialize a new Simple project in the given directory
pub fn init_project(dir: &Path, name: Option<&str>) -> PkgResult<()> {
    let manifest_path = dir.join("simple.toml");

    // Check if already initialized
    if manifest_path.exists() {
        return Err(PkgError::AlreadyInitialized(dir.display().to_string()));
    }

    // Determine project name
    let project_name = name
        .map(|s| s.to_string())
        .or_else(|| {
            dir.file_name()
                .and_then(|n| n.to_str())
                .map(|s| s.to_string())
        })
        .unwrap_or_else(|| "my-project".to_string());

    // Create manifest
    let manifest = Manifest::new(&project_name);
    manifest.save(&manifest_path)?;

    // Create src directory and main.spl
    let src_dir = dir.join("src");
    std::fs::create_dir_all(&src_dir)?;

    let main_file = src_dir.join("main.spl");
    if !main_file.exists() {
        std::fs::write(&main_file, DEFAULT_MAIN)?;
    }

    Ok(())
}

const DEFAULT_MAIN: &str = r#"# Simple Language Project
# Run with: simple run

fn main() -> i32:
    print("Hello, Simple!")
    return 0
"#;

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_init_project() {
        let temp_dir = std::env::temp_dir().join("simple-init-test");
        let _ = fs::remove_dir_all(&temp_dir);
        fs::create_dir_all(&temp_dir).unwrap();

        init_project(&temp_dir, Some("myapp")).unwrap();

        // Check manifest was created
        let manifest_path = temp_dir.join("simple.toml");
        assert!(manifest_path.exists());

        // Check manifest content
        let manifest = Manifest::load(&manifest_path).unwrap();
        assert_eq!(manifest.package.name, "myapp");

        // Check src/main.spl was created
        let main_path = temp_dir.join("src/main.spl");
        assert!(main_path.exists());

        // Cleanup
        let _ = fs::remove_dir_all(&temp_dir);
    }

    #[test]
    fn test_init_already_initialized() {
        let temp_dir = std::env::temp_dir().join("simple-init-test-existing");
        let _ = fs::remove_dir_all(&temp_dir);
        fs::create_dir_all(&temp_dir).unwrap();

        // First init should succeed
        init_project(&temp_dir, Some("myapp")).unwrap();

        // Second init should fail
        let result = init_project(&temp_dir, Some("myapp"));
        assert!(matches!(result, Err(PkgError::AlreadyInitialized(_))));

        // Cleanup
        let _ = fs::remove_dir_all(&temp_dir);
    }

    #[test]
    fn test_init_uses_dir_name() {
        let temp_dir = std::env::temp_dir().join("my-cool-project");
        let _ = fs::remove_dir_all(&temp_dir);
        fs::create_dir_all(&temp_dir).unwrap();

        init_project(&temp_dir, None).unwrap();

        let manifest = Manifest::load(&temp_dir.join("simple.toml")).unwrap();
        assert_eq!(manifest.package.name, "my-cool-project");

        // Cleanup
        let _ = fs::remove_dir_all(&temp_dir);
    }
}
