//! Virtual environment management for Simple projects.
//!
//! Provides isolated dependency environments similar to Python virtualenv
//! or Node.js node_modules.
//!
//! ## Usage
//!
//! ```bash
//! simple env create myproject     # Create environment
//! simple env activate myproject   # Print activation script
//! simple env list                 # List environments
//! simple env remove myproject     # Remove environment
//! ```

use std::fs;
use std::path::{Path, PathBuf};

/// Environment configuration
#[derive(Debug)]
pub struct Environment {
    /// Environment name
    pub name: String,
    /// Environment directory
    pub path: PathBuf,
    /// Whether the environment is active
    pub active: bool,
}

impl Environment {
    /// Get the base directory for all environments
    pub fn base_dir() -> PathBuf {
        dirs::data_local_dir()
            .unwrap_or_else(|| PathBuf::from("."))
            .join("simple")
            .join("envs")
    }

    /// Get environment directory by name
    pub fn env_dir(name: &str) -> PathBuf {
        Self::base_dir().join(name)
    }

    /// Check if an environment exists
    pub fn exists(name: &str) -> bool {
        Self::env_dir(name).exists()
    }

    /// Load environment metadata
    pub fn load(name: &str) -> Option<Self> {
        let path = Self::env_dir(name);
        if !path.exists() {
            return None;
        }

        Some(Environment {
            name: name.to_string(),
            path,
            active: Self::is_active(name),
        })
    }

    /// Check if this environment is currently active
    fn is_active(name: &str) -> bool {
        std::env::var("SIMPLE_ENV").map(|v| v == name).unwrap_or(false)
    }
}

/// Create a new virtual environment
pub fn create_env(name: &str) -> i32 {
    let env_dir = Environment::env_dir(name);

    if env_dir.exists() {
        eprintln!("error: environment '{}' already exists", name);
        eprintln!("Use 'simple env remove {}' to remove it first", name);
        return 1;
    }

    // Create environment directory structure
    let lib_dir = env_dir.join("lib");
    let bin_dir = env_dir.join("bin");
    let cache_dir = env_dir.join("cache");

    if let Err(e) = fs::create_dir_all(&lib_dir) {
        eprintln!("error: failed to create lib directory: {}", e);
        return 1;
    }

    if let Err(e) = fs::create_dir_all(&bin_dir) {
        eprintln!("error: failed to create bin directory: {}", e);
        return 1;
    }

    if let Err(e) = fs::create_dir_all(&cache_dir) {
        eprintln!("error: failed to create cache directory: {}", e);
        return 1;
    }

    // Create environment config file
    let config_path = env_dir.join("env.toml");
    let created = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    let config_content = format!(
        r#"# Simple Environment Configuration
name = "{}"
version = "1"
created = "{}"

[paths]
lib = "lib"
bin = "bin"
cache = "cache"
"#,
        name, created
    );

    if let Err(e) = fs::write(&config_path, config_content) {
        eprintln!("error: failed to create config file: {}", e);
        return 1;
    }

    // Create activation scripts
    create_activation_scripts(&env_dir, name);

    println!("Created environment '{}' at {}", name, env_dir.display());
    println!();
    println!("To activate this environment:");
    println!("  source $(simple env activate {})", name);
    println!();
    println!("Or manually set:");
    println!("  export SIMPLE_ENV={}", name);
    println!("  export SIMPLE_LIB={}", lib_dir.display());

    0
}

/// Create shell activation scripts
fn create_activation_scripts(env_dir: &Path, name: &str) {
    let lib_dir = env_dir.join("lib");
    let bin_dir = env_dir.join("bin");

    // Bash/Zsh activation script
    let activate_sh = format!(
        r#"#!/bin/bash
# Simple environment activation script for {}

export SIMPLE_ENV="{}"
export SIMPLE_LIB="{}"
export PATH="{}:$PATH"

# Deactivation function
deactivate_simple() {{
    unset SIMPLE_ENV
    unset SIMPLE_LIB
    export PATH=$(echo "$PATH" | sed -e 's|{}:||g')
    unset -f deactivate_simple
}}

echo "Activated Simple environment: {}"
"#,
        name,
        name,
        lib_dir.display(),
        bin_dir.display(),
        bin_dir.display(),
        name
    );

    let _ = fs::write(env_dir.join("activate.sh"), activate_sh);

    // Fish activation script
    let activate_fish = format!(
        r#"# Simple environment activation script for {}

set -gx SIMPLE_ENV "{}"
set -gx SIMPLE_LIB "{}"
set -gx PATH "{}" $PATH

function deactivate_simple
    set -e SIMPLE_ENV
    set -e SIMPLE_LIB
    set PATH (string match -v "{}" $PATH)
    functions -e deactivate_simple
end

echo "Activated Simple environment: {}"
"#,
        name,
        name,
        lib_dir.display(),
        bin_dir.display(),
        bin_dir.display(),
        name
    );

    let _ = fs::write(env_dir.join("activate.fish"), activate_fish);
}

/// Print activation script path
pub fn activate_env(name: &str, shell: Option<&str>) -> i32 {
    let env_dir = Environment::env_dir(name);

    if !env_dir.exists() {
        eprintln!("error: environment '{}' does not exist", name);
        eprintln!("Use 'simple env create {}' to create it", name);
        return 1;
    }

    // Detect shell or use provided
    let shell = shell.unwrap_or_else(|| {
        std::env::var("SHELL")
            .map(|s| if s.contains("fish") { "fish" } else { "bash" })
            .unwrap_or("bash")
    });

    let script = if shell == "fish" {
        env_dir.join("activate.fish")
    } else {
        env_dir.join("activate.sh")
    };

    // Print the script path for sourcing
    println!("{}", script.display());
    0
}

/// List all environments
pub fn list_envs() -> i32 {
    let base_dir = Environment::base_dir();

    if !base_dir.exists() {
        println!("No environments found.");
        println!("Use 'simple env create <name>' to create one.");
        return 0;
    }

    let entries: Vec<_> = fs::read_dir(&base_dir)
        .into_iter()
        .flatten()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().is_dir())
        .collect();

    if entries.is_empty() {
        println!("No environments found.");
        println!("Use 'simple env create <name>' to create one.");
        return 0;
    }

    println!("Simple Environments:");
    println!();

    let current_env = std::env::var("SIMPLE_ENV").ok();

    for entry in entries {
        let name = entry.file_name().to_string_lossy().to_string();
        let active = current_env.as_ref().map(|e| e == &name).unwrap_or(false);
        let marker = if active { "*" } else { " " };

        println!("  {} {}", marker, name);
    }

    println!();
    if current_env.is_some() {
        println!("* = currently active");
    }

    0
}

/// Remove an environment
pub fn remove_env(name: &str, force: bool) -> i32 {
    let env_dir = Environment::env_dir(name);

    if !env_dir.exists() {
        eprintln!("error: environment '{}' does not exist", name);
        return 1;
    }

    // Check if environment is active
    if Environment::is_active(name) && !force {
        eprintln!("error: environment '{}' is currently active", name);
        eprintln!("Deactivate it first or use --force");
        return 1;
    }

    if let Err(e) = fs::remove_dir_all(&env_dir) {
        eprintln!("error: failed to remove environment: {}", e);
        return 1;
    }

    println!("Removed environment '{}'", name);
    0
}

/// Print environment info
pub fn env_info(name: &str) -> i32 {
    let env = match Environment::load(name) {
        Some(e) => e,
        None => {
            eprintln!("error: environment '{}' does not exist", name);
            return 1;
        }
    };

    println!("Environment: {}", env.name);
    println!("Path: {}", env.path.display());
    println!("Active: {}", if env.active { "yes" } else { "no" });
    println!();
    println!("Directories:");
    println!("  lib:   {}", env.path.join("lib").display());
    println!("  bin:   {}", env.path.join("bin").display());
    println!("  cache: {}", env.path.join("cache").display());

    0
}

// Add dirs crate for cross-platform paths
mod dirs {
    use std::path::PathBuf;

    pub fn data_local_dir() -> Option<PathBuf> {
        #[cfg(target_os = "linux")]
        {
            std::env::var("XDG_DATA_HOME").map(PathBuf::from).ok().or_else(|| {
                std::env::var("HOME")
                    .map(|h| PathBuf::from(h).join(".local/share"))
                    .ok()
            })
        }

        #[cfg(target_os = "macos")]
        {
            std::env::var("HOME")
                .map(|h| PathBuf::from(h).join("Library/Application Support"))
                .ok()
        }

        #[cfg(target_os = "windows")]
        {
            std::env::var("LOCALAPPDATA").map(PathBuf::from).ok()
        }

        #[cfg(not(any(target_os = "linux", target_os = "macos", target_os = "windows")))]
        {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_environment_base_dir() {
        let base = Environment::base_dir();
        assert!(base.to_string_lossy().contains("simple"));
    }

    #[test]
    fn test_environment_env_dir() {
        let dir = Environment::env_dir("test-env");
        assert!(dir.to_string_lossy().contains("test-env"));
    }
}
