//! Fluent builder for linker invocation.
//!
//! Provides a convenient builder pattern for configuring and executing
//! native linking operations.
//!
//! # Example
//!
//! ```ignore
//! use simple_compiler::linker::{LinkerBuilder, NativeLinker};
//!
//! let result = LinkerBuilder::new()
//!     .linker(NativeLinker::Mold)
//!     .object("main.o")
//!     .object("lib.o")
//!     .output("program")
//!     .library("c")
//!     .pie()
//!     .link();
//! ```

use std::path::{Path, PathBuf};

use super::error::{LinkerError, LinkerResult};
use super::native::{LinkOptions, NativeLinker};

/// Builder for native linker invocation.
#[derive(Debug, Clone)]
pub struct LinkerBuilder {
    /// Selected linker (auto-detected if None).
    linker: Option<NativeLinker>,
    /// Object files to link.
    objects: Vec<PathBuf>,
    /// Output file path.
    output: Option<PathBuf>,
    /// Link options.
    options: LinkOptions,
}

impl LinkerBuilder {
    /// Create a new linker builder.
    pub fn new() -> Self {
        Self {
            linker: None,
            objects: Vec::new(),
            output: None,
            options: LinkOptions::new(),
        }
    }

    /// Set the linker to use.
    ///
    /// If not set, the best available linker will be auto-detected.
    pub fn linker(mut self, linker: NativeLinker) -> Self {
        self.linker = Some(linker);
        self
    }

    /// Set the linker by name.
    ///
    /// Returns an error if the linker name is not recognized.
    pub fn linker_name(mut self, name: &str) -> LinkerResult<Self> {
        self.linker = Some(NativeLinker::from_name(name).ok_or_else(|| LinkerError::LinkerNotFound(name.to_string()))?);
        Ok(self)
    }

    /// Add an object file to link.
    pub fn object(mut self, path: impl Into<PathBuf>) -> Self {
        self.objects.push(path.into());
        self
    }

    /// Add multiple object files to link.
    pub fn objects<I, P>(mut self, paths: I) -> Self
    where
        I: IntoIterator<Item = P>,
        P: Into<PathBuf>,
    {
        self.objects.extend(paths.into_iter().map(|p| p.into()));
        self
    }

    /// Set the output file path.
    pub fn output(mut self, path: impl Into<PathBuf>) -> Self {
        self.output = Some(path.into());
        self
    }

    /// Add a library to link against.
    pub fn library(mut self, name: impl Into<String>) -> Self {
        self.options.libraries.push(name.into());
        self
    }

    /// Add multiple libraries to link against.
    pub fn libraries<I, S>(mut self, names: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.options.libraries.extend(names.into_iter().map(|s| s.into()));
        self
    }

    /// Add a library search path.
    pub fn library_path(mut self, path: impl Into<PathBuf>) -> Self {
        self.options.library_paths.push(path.into());
        self
    }

    /// Add multiple library search paths.
    pub fn library_paths<I, P>(mut self, paths: I) -> Self
    where
        I: IntoIterator<Item = P>,
        P: Into<PathBuf>,
    {
        self.options.library_paths.extend(paths.into_iter().map(|p| p.into()));
        self
    }

    /// Enable linker map file generation.
    pub fn map(mut self, path: impl Into<PathBuf>) -> Self {
        self.options.generate_map = true;
        self.options.map_file = Some(path.into());
        self
    }

    /// Enable automatic map file generation.
    ///
    /// The map file will be named `<output>.map`.
    pub fn auto_map(mut self) -> Self {
        self.options.generate_map = true;
        self
    }

    /// Strip symbols from the output.
    pub fn strip(mut self) -> Self {
        self.options.strip = true;
        self
    }

    /// Create a shared library.
    pub fn shared(mut self) -> Self {
        self.options.shared = true;
        self
    }

    /// Create a position-independent executable.
    pub fn pie(mut self) -> Self {
        self.options.pie = true;
        self
    }

    /// Set the number of threads for parallel linking.
    pub fn threads(mut self, n: usize) -> Self {
        self.options.threads = Some(n);
        self
    }

    /// Enable verbose output.
    pub fn verbose(mut self) -> Self {
        self.options.verbose = true;
        self
    }

    /// Add an extra linker flag.
    pub fn flag(mut self, flag: impl Into<String>) -> Self {
        self.options.extra_flags.push(flag.into());
        self
    }

    /// Add multiple extra linker flags.
    pub fn flags<I, S>(mut self, flags: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: Into<String>,
    {
        self.options.extra_flags.extend(flags.into_iter().map(|s| s.into()));
        self
    }

    /// Execute the linker.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - No output file is specified
    /// - No object files are specified
    /// - No linker is available
    /// - Linking fails
    pub fn link(mut self) -> LinkerResult<()> {
        // Validate configuration
        let output = self
            .output
            .as_ref()
            .ok_or_else(|| LinkerError::InvalidConfig("no output file specified".to_string()))?;

        if self.objects.is_empty() {
            return Err(LinkerError::InvalidConfig("no object files specified".to_string()));
        }

        // Detect linker if not specified
        let linker = match self.linker {
            Some(l) => l,
            None => NativeLinker::detect().ok_or(LinkerError::NoLinkerFound)?,
        };

        // Set up auto-map if needed
        if self.options.generate_map && self.options.map_file.is_none() {
            self.options.map_file = Some(output.with_extension("map"));
        }

        // Execute linking
        linker.link(&self.objects, output, &self.options)
    }

    /// Get the linker that would be used.
    ///
    /// Returns the explicitly set linker, or auto-detects one.
    pub fn get_linker(&self) -> Option<NativeLinker> {
        self.linker.or_else(NativeLinker::detect)
    }

    /// Check if the builder is ready to link.
    pub fn is_ready(&self) -> bool {
        self.output.is_some() && !self.objects.is_empty() && self.get_linker().is_some()
    }
}

impl Default for LinkerBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Convenience function to link object files.
///
/// Uses auto-detected linker with default options.
pub fn link_objects(objects: &[impl AsRef<Path>], output: impl AsRef<Path>) -> LinkerResult<()> {
    LinkerBuilder::new()
        .objects(objects.iter().map(|p| p.as_ref().to_path_buf()))
        .output(output.as_ref())
        .link()
}

/// Convenience function to link object files with the specified linker.
pub fn link_with(linker: NativeLinker, objects: &[impl AsRef<Path>], output: impl AsRef<Path>) -> LinkerResult<()> {
    LinkerBuilder::new()
        .linker(linker)
        .objects(objects.iter().map(|p| p.as_ref().to_path_buf()))
        .output(output.as_ref())
        .link()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_builder_creation() {
        let builder = LinkerBuilder::new();
        assert!(builder.linker.is_none());
        assert!(builder.objects.is_empty());
        assert!(builder.output.is_none());
    }

    #[test]
    fn test_builder_fluent_api() {
        let builder = LinkerBuilder::new()
            .linker(NativeLinker::Mold)
            .object("a.o")
            .object("b.o")
            .output("program")
            .library("c")
            .library_path("/usr/lib")
            .strip()
            .pie()
            .threads(4)
            .verbose()
            .flag("--gc-sections");

        assert_eq!(builder.linker, Some(NativeLinker::Mold));
        assert_eq!(builder.objects.len(), 2);
        assert_eq!(builder.output, Some(PathBuf::from("program")));
        assert_eq!(builder.options.libraries, vec!["c"]);
        assert_eq!(builder.options.library_paths, vec![PathBuf::from("/usr/lib")]);
        assert!(builder.options.strip);
        assert!(builder.options.pie);
        assert_eq!(builder.options.threads, Some(4));
        assert!(builder.options.verbose);
        assert_eq!(builder.options.extra_flags, vec!["--gc-sections"]);
    }

    #[test]
    fn test_builder_objects_batch() {
        let builder = LinkerBuilder::new().objects(["a.o", "b.o", "c.o"]);

        assert_eq!(builder.objects.len(), 3);
    }

    #[test]
    fn test_builder_libraries_batch() {
        let builder = LinkerBuilder::new().libraries(["c", "m", "pthread"]);

        assert_eq!(builder.options.libraries, vec!["c", "m", "pthread"]);
    }

    #[test]
    fn test_builder_linker_name() {
        let builder = LinkerBuilder::new().linker_name("mold").unwrap();
        assert_eq!(builder.linker, Some(NativeLinker::Mold));

        let result = LinkerBuilder::new().linker_name("nonexistent");
        assert!(result.is_err());
    }

    #[test]
    fn test_builder_is_ready() {
        let builder = LinkerBuilder::new();
        assert!(!builder.is_ready());

        let builder = LinkerBuilder::new().object("a.o").output("out");
        // May be ready depending on system linker availability
        let _ = builder.is_ready();
    }

    #[test]
    fn test_builder_auto_map() {
        let builder = LinkerBuilder::new().output("program").auto_map();

        assert!(builder.options.generate_map);
        assert!(builder.options.map_file.is_none()); // Set during link()
    }

    #[test]
    fn test_link_validation_no_output() {
        let result = LinkerBuilder::new().object("a.o").link();

        assert!(matches!(result, Err(LinkerError::InvalidConfig(_))));
    }

    #[test]
    fn test_link_validation_no_objects() {
        let result = LinkerBuilder::new().output("program").link();

        assert!(matches!(result, Err(LinkerError::InvalidConfig(_))));
    }
}
