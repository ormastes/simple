//! Native library cross-compilation support.
//!
//! This module provides utilities for building native libraries
//! for different target architectures.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use simple_common::target::{Target, TargetArch, TargetOS};

/// Error type for cross-compilation operations.
#[derive(Debug)]
pub enum CrossCompileError {
    /// Toolchain not found.
    ToolchainNotFound(String),
    /// Build failed.
    BuildFailed(String),
    /// Unsupported target.
    UnsupportedTarget(Target),
    /// I/O error.
    IoError(std::io::Error),
    /// Configuration error.
    ConfigError(String),
}

impl std::fmt::Display for CrossCompileError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CrossCompileError::ToolchainNotFound(tc) => {
                write!(f, "Toolchain not found: {}", tc)
            }
            CrossCompileError::BuildFailed(msg) => {
                write!(f, "Build failed: {}", msg)
            }
            CrossCompileError::UnsupportedTarget(target) => {
                write!(f, "Unsupported target: {}", target)
            }
            CrossCompileError::IoError(e) => {
                write!(f, "I/O error: {}", e)
            }
            CrossCompileError::ConfigError(msg) => {
                write!(f, "Configuration error: {}", msg)
            }
        }
    }
}

impl std::error::Error for CrossCompileError {}

impl From<std::io::Error> for CrossCompileError {
    fn from(e: std::io::Error) -> Self {
        CrossCompileError::IoError(e)
    }
}

/// Toolchain specification for a target.
#[derive(Debug, Clone)]
pub struct Toolchain {
    /// Target this toolchain is for.
    pub target: Target,
    /// C compiler path.
    pub cc: PathBuf,
    /// C++ compiler path (optional).
    pub cxx: Option<PathBuf>,
    /// Archiver path.
    pub ar: PathBuf,
    /// Linker path (defaults to cc).
    pub ld: Option<PathBuf>,
    /// Sysroot path (optional).
    pub sysroot: Option<PathBuf>,
    /// Extra compiler flags.
    pub cflags: Vec<String>,
    /// Extra linker flags.
    pub ldflags: Vec<String>,
}

impl Toolchain {
    /// Create a toolchain for the host target (uses system defaults).
    pub fn host() -> Self {
        Self {
            target: Target::host(),
            cc: PathBuf::from("cc"),
            cxx: Some(PathBuf::from("c++")),
            ar: PathBuf::from("ar"),
            ld: None,
            sysroot: None,
            cflags: Vec::new(),
            ldflags: Vec::new(),
        }
    }

    /// Create a toolchain for a cross-compilation target.
    pub fn for_target(target: Target) -> Option<Self> {
        let prefix = Self::get_toolchain_prefix(target)?;

        Some(Self {
            target,
            cc: PathBuf::from(format!("{}-gcc", prefix)),
            cxx: Some(PathBuf::from(format!("{}-g++", prefix))),
            ar: PathBuf::from(format!("{}-ar", prefix)),
            ld: Some(PathBuf::from(format!("{}-ld", prefix))),
            sysroot: None,
            cflags: Vec::new(),
            ldflags: Vec::new(),
        })
    }

    /// Get the standard toolchain prefix for a target.
    fn get_toolchain_prefix(target: Target) -> Option<&'static str> {
        match (target.arch, target.os) {
            (TargetArch::X86_64, TargetOS::Linux) => Some("x86_64-linux-gnu"),
            (TargetArch::Aarch64, TargetOS::Linux) => Some("aarch64-linux-gnu"),
            (TargetArch::X86, TargetOS::Linux) => Some("i686-linux-gnu"),
            (TargetArch::Arm, TargetOS::Linux) => Some("arm-linux-gnueabihf"),
            (TargetArch::Riscv64, TargetOS::Linux) => Some("riscv64-linux-gnu"),
            (TargetArch::Riscv32, TargetOS::Linux) => Some("riscv32-linux-gnu"),
            // Add more targets as needed
            _ => None,
        }
    }

    /// Check if this toolchain is available on the system.
    pub fn is_available(&self) -> bool {
        // Check if the C compiler exists and is executable
        Command::new(&self.cc)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    /// Set the sysroot.
    pub fn with_sysroot(mut self, sysroot: impl Into<PathBuf>) -> Self {
        self.sysroot = Some(sysroot.into());
        self.cflags.push(format!(
            "--sysroot={}",
            self.sysroot.as_ref().unwrap().display()
        ));
        self.ldflags.push(format!(
            "--sysroot={}",
            self.sysroot.as_ref().unwrap().display()
        ));
        self
    }

    /// Add extra C flags.
    pub fn with_cflags(mut self, flags: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.cflags.extend(flags.into_iter().map(Into::into));
        self
    }

    /// Add extra linker flags.
    pub fn with_ldflags(mut self, flags: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.ldflags.extend(flags.into_iter().map(Into::into));
        self
    }

    /// Get the linker (defaults to cc if not specified).
    pub fn linker(&self) -> &Path {
        self.ld.as_ref().unwrap_or(&self.cc)
    }
}

/// Native library build configuration.
#[derive(Debug, Clone)]
pub struct NativeLibConfig {
    /// Library name.
    pub name: String,
    /// Source files.
    pub sources: Vec<PathBuf>,
    /// Include directories.
    pub include_dirs: Vec<PathBuf>,
    /// Library dependencies.
    pub libs: Vec<String>,
    /// Library search paths.
    pub lib_dirs: Vec<PathBuf>,
    /// Extra compiler flags.
    pub cflags: Vec<String>,
    /// Extra linker flags.
    pub ldflags: Vec<String>,
    /// Build as shared library.
    pub shared: bool,
    /// Output directory.
    pub output_dir: PathBuf,
}

impl NativeLibConfig {
    /// Create a new library configuration.
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            sources: Vec::new(),
            include_dirs: Vec::new(),
            libs: Vec::new(),
            lib_dirs: Vec::new(),
            cflags: Vec::new(),
            ldflags: Vec::new(),
            shared: true,
            output_dir: PathBuf::from("."),
        }
    }

    /// Add a source file.
    pub fn source(mut self, path: impl Into<PathBuf>) -> Self {
        self.sources.push(path.into());
        self
    }

    /// Add multiple source files.
    pub fn sources(mut self, paths: impl IntoIterator<Item = impl Into<PathBuf>>) -> Self {
        self.sources.extend(paths.into_iter().map(Into::into));
        self
    }

    /// Add an include directory.
    pub fn include_dir(mut self, path: impl Into<PathBuf>) -> Self {
        self.include_dirs.push(path.into());
        self
    }

    /// Link to a library.
    pub fn link(mut self, lib: impl Into<String>) -> Self {
        self.libs.push(lib.into());
        self
    }

    /// Add a library search path.
    pub fn lib_dir(mut self, path: impl Into<PathBuf>) -> Self {
        self.lib_dirs.push(path.into());
        self
    }

    /// Add extra compiler flags.
    pub fn cflags(mut self, flags: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.cflags.extend(flags.into_iter().map(Into::into));
        self
    }

    /// Add extra linker flags.
    pub fn ldflags(mut self, flags: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.ldflags.extend(flags.into_iter().map(Into::into));
        self
    }

    /// Build as static library.
    pub fn static_lib(mut self) -> Self {
        self.shared = false;
        self
    }

    /// Build as shared library.
    pub fn shared_lib(mut self) -> Self {
        self.shared = true;
        self
    }

    /// Set the output directory.
    pub fn output_dir(mut self, path: impl Into<PathBuf>) -> Self {
        self.output_dir = path.into();
        self
    }

    /// Get the output file name for the target.
    pub fn output_file(&self, target: Target) -> PathBuf {
        let ext = match (self.shared, target.os) {
            (true, TargetOS::Windows) => "dll",
            (true, TargetOS::MacOS) => "dylib",
            (true, _) => "so",
            (false, TargetOS::Windows) => "lib",
            (false, _) => "a",
        };

        let prefix = if !self.shared && target.os != TargetOS::Windows {
            "lib"
        } else if self.shared && target.os != TargetOS::Windows {
            "lib"
        } else {
            ""
        };

        self.output_dir
            .join(format!("{}{}.{}", prefix, self.name, ext))
    }
}

/// Native library builder.
pub struct NativeLibBuilder {
    /// Toolchain to use.
    toolchain: Toolchain,
    /// Build configuration.
    config: NativeLibConfig,
    /// Object files directory.
    obj_dir: PathBuf,
}

impl NativeLibBuilder {
    /// Create a new builder.
    pub fn new(toolchain: Toolchain, config: NativeLibConfig) -> Self {
        let obj_dir = config.output_dir.join("obj");
        Self {
            toolchain,
            config,
            obj_dir,
        }
    }

    /// Build the library.
    pub fn build(&self) -> Result<PathBuf, CrossCompileError> {
        // Check toolchain availability
        if !self.toolchain.is_available() {
            return Err(CrossCompileError::ToolchainNotFound(
                self.toolchain.cc.display().to_string(),
            ));
        }

        // Create directories
        std::fs::create_dir_all(&self.obj_dir)?;
        std::fs::create_dir_all(&self.config.output_dir)?;

        // Compile each source file
        let mut objects = Vec::new();
        for source in &self.config.sources {
            let obj = self.compile_source(source)?;
            objects.push(obj);
        }

        // Link
        let output = if self.config.shared {
            self.link_shared(&objects)?
        } else {
            self.link_static(&objects)?
        };

        Ok(output)
    }

    /// Compile a single source file to object.
    fn compile_source(&self, source: &Path) -> Result<PathBuf, CrossCompileError> {
        let stem = source.file_stem().ok_or_else(|| {
            CrossCompileError::ConfigError("Invalid source file name".to_string())
        })?;
        let obj = self.obj_dir.join(format!("{}.o", stem.to_string_lossy()));

        let mut cmd = Command::new(&self.toolchain.cc);
        cmd.arg("-c").arg("-o").arg(&obj).arg(source);

        // Add include directories
        for inc in &self.config.include_dirs {
            cmd.arg(format!("-I{}", inc.display()));
        }

        // Add toolchain flags
        for flag in &self.toolchain.cflags {
            cmd.arg(flag);
        }

        // Add config flags
        for flag in &self.config.cflags {
            cmd.arg(flag);
        }

        // Position independent code for shared libs
        if self.config.shared {
            cmd.arg("-fPIC");
        }

        let output = cmd.output()?;
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(CrossCompileError::BuildFailed(format!(
                "Compilation of {} failed: {}",
                source.display(),
                stderr
            )));
        }

        Ok(obj)
    }

    /// Link object files into a shared library.
    fn link_shared(&self, objects: &[PathBuf]) -> Result<PathBuf, CrossCompileError> {
        let output = self.config.output_file(self.toolchain.target);

        let mut cmd = Command::new(&self.toolchain.cc);
        cmd.arg("-shared").arg("-o").arg(&output);

        // Add objects
        for obj in objects {
            cmd.arg(obj);
        }

        // Add library search paths
        for lib_dir in &self.config.lib_dirs {
            cmd.arg(format!("-L{}", lib_dir.display()));
        }

        // Add libraries
        for lib in &self.config.libs {
            cmd.arg(format!("-l{}", lib));
        }

        // Add toolchain flags
        for flag in &self.toolchain.ldflags {
            cmd.arg(flag);
        }

        // Add config flags
        for flag in &self.config.ldflags {
            cmd.arg(flag);
        }

        let output_result = cmd.output()?;
        if !output_result.status.success() {
            let stderr = String::from_utf8_lossy(&output_result.stderr);
            return Err(CrossCompileError::BuildFailed(format!(
                "Linking failed: {}",
                stderr
            )));
        }

        Ok(output)
    }

    /// Create a static library from object files.
    fn link_static(&self, objects: &[PathBuf]) -> Result<PathBuf, CrossCompileError> {
        let output = self.config.output_file(self.toolchain.target);

        let mut cmd = Command::new(&self.toolchain.ar);
        cmd.arg("rcs").arg(&output);

        for obj in objects {
            cmd.arg(obj);
        }

        let output_result = cmd.output()?;
        if !output_result.status.success() {
            let stderr = String::from_utf8_lossy(&output_result.stderr);
            return Err(CrossCompileError::BuildFailed(format!(
                "Archive creation failed: {}",
                stderr
            )));
        }

        Ok(output)
    }
}

/// Toolchain registry for multiple targets.
#[derive(Debug, Default)]
pub struct ToolchainRegistry {
    /// Registered toolchains.
    toolchains: HashMap<Target, Toolchain>,
}

impl ToolchainRegistry {
    /// Create a new registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register the host toolchain.
    pub fn register_host(&mut self) {
        self.toolchains.insert(Target::host(), Toolchain::host());
    }

    /// Register a toolchain for a target.
    pub fn register(&mut self, toolchain: Toolchain) {
        self.toolchains.insert(toolchain.target, toolchain);
    }

    /// Auto-detect available toolchains.
    pub fn detect_available(&mut self) {
        // Try to detect common cross-compilation targets
        let targets = [
            Target::new(TargetArch::X86_64, TargetOS::Linux),
            Target::new(TargetArch::Aarch64, TargetOS::Linux),
            Target::new(TargetArch::X86, TargetOS::Linux),
            Target::new(TargetArch::Arm, TargetOS::Linux),
            Target::new(TargetArch::Riscv64, TargetOS::Linux),
        ];

        for target in targets {
            if let Some(tc) = Toolchain::for_target(target) {
                if tc.is_available() {
                    self.toolchains.insert(target, tc);
                }
            }
        }
    }

    /// Get a toolchain for a target.
    pub fn get(&self, target: Target) -> Option<&Toolchain> {
        self.toolchains.get(&target)
    }

    /// Check if a toolchain is available for a target.
    pub fn has_target(&self, target: Target) -> bool {
        self.toolchains.contains_key(&target)
    }

    /// Get all available targets.
    pub fn available_targets(&self) -> Vec<Target> {
        self.toolchains.keys().copied().collect()
    }
}

/// Build native libraries for multiple targets.
pub fn build_for_targets(
    config: &NativeLibConfig,
    targets: &[Target],
    registry: &ToolchainRegistry,
) -> Result<HashMap<Target, PathBuf>, CrossCompileError> {
    let mut results = HashMap::new();

    for &target in targets {
        let toolchain = registry
            .get(target)
            .ok_or(CrossCompileError::UnsupportedTarget(target))?;

        // Create target-specific output directory
        let mut target_config = config.clone();
        target_config.output_dir = config.output_dir.join(target.to_string());

        let builder = NativeLibBuilder::new(toolchain.clone(), target_config);
        let output = builder.build()?;

        results.insert(target, output);
    }

    Ok(results)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_toolchain_host() {
        let tc = Toolchain::host();
        assert_eq!(tc.target, Target::host());
    }

    #[test]
    fn test_toolchain_prefix() {
        let target = Target::new(TargetArch::Aarch64, TargetOS::Linux);
        let tc = Toolchain::for_target(target);
        assert!(tc.is_some());

        let tc = tc.unwrap();
        assert!(tc.cc.to_string_lossy().contains("aarch64"));
    }

    #[test]
    fn test_native_lib_config() {
        let config = NativeLibConfig::new("test")
            .source("test.c")
            .include_dir("/usr/include")
            .link("m")
            .shared_lib();

        assert_eq!(config.name, "test");
        assert!(config.shared);
        assert_eq!(config.sources.len(), 1);
    }

    #[test]
    fn test_output_file_names() {
        let config = NativeLibConfig::new("test").shared_lib();

        let linux = config.output_file(Target::new(TargetArch::X86_64, TargetOS::Linux));
        assert!(linux.to_string_lossy().ends_with(".so"));

        let windows = config.output_file(Target::new(TargetArch::X86_64, TargetOS::Windows));
        assert!(windows.to_string_lossy().ends_with(".dll"));

        let macos = config.output_file(Target::new(TargetArch::Aarch64, TargetOS::MacOS));
        assert!(macos.to_string_lossy().ends_with(".dylib"));
    }

    #[test]
    fn test_static_lib_output() {
        let config = NativeLibConfig::new("test").static_lib();

        let linux = config.output_file(Target::new(TargetArch::X86_64, TargetOS::Linux));
        assert!(linux.to_string_lossy().ends_with(".a"));
    }

    #[test]
    fn test_toolchain_registry() {
        let mut registry = ToolchainRegistry::new();
        registry.register_host();

        assert!(registry.has_target(Target::host()));
        assert!(registry.get(Target::host()).is_some());
    }

    #[test]
    fn test_cross_compile_error_display() {
        let err = CrossCompileError::ToolchainNotFound("gcc".to_string());
        assert!(err.to_string().contains("gcc"));

        let err = CrossCompileError::UnsupportedTarget(Target::host());
        assert!(!err.to_string().is_empty());
    }
}
