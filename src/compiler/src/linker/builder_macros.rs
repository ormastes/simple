//! Shared macros for builder patterns.
//!
//! This module provides macros to reduce duplication in builder implementations
//! for `LinkerBuilder`, `NativeBinaryBuilder`, and `NativeBinaryOptions`.

/// Generate common linker builder methods.
///
/// This macro generates methods for library linking and path management
/// that are shared across multiple builder types.
///
/// # Usage
///
/// ```ignore
/// impl MyBuilder {
///     impl_linker_builder_methods!(options); // uses self.options.libraries, etc.
/// }
/// ```
///
/// Or with direct field access:
///
/// ```ignore
/// impl MyOptions {
///     impl_linker_builder_methods!(self); // uses self.libraries directly
/// }
/// ```
#[macro_export]
macro_rules! impl_linker_builder_methods {
    // Variant for builders with `self.options` containing the fields
    (options) => {
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
        pub fn library_path(mut self, path: impl Into<std::path::PathBuf>) -> Self {
            self.options.library_paths.push(path.into());
            self
        }

        /// Add multiple library search paths.
        pub fn library_paths<I, P>(mut self, paths: I) -> Self
        where
            I: IntoIterator<Item = P>,
            P: Into<std::path::PathBuf>,
        {
            self.options.library_paths.extend(paths.into_iter().map(|p| p.into()));
            self
        }
    };

    // Variant for option structs with direct field access
    (direct) => {
        /// Add a library to link against.
        pub fn library(mut self, name: impl Into<String>) -> Self {
            self.libraries.push(name.into());
            self
        }

        /// Add multiple libraries to link against.
        pub fn libraries<I, S>(mut self, names: I) -> Self
        where
            I: IntoIterator<Item = S>,
            S: Into<String>,
        {
            self.libraries.extend(names.into_iter().map(|s| s.into()));
            self
        }

        /// Add a library search path.
        pub fn library_path(mut self, path: impl Into<std::path::PathBuf>) -> Self {
            self.library_paths.push(path.into());
            self
        }

        /// Add multiple library search paths.
        pub fn library_paths<I, P>(mut self, paths: I) -> Self
        where
            I: IntoIterator<Item = P>,
            P: Into<std::path::PathBuf>,
        {
            self.library_paths.extend(paths.into_iter().map(|p| p.into()));
            self
        }
    };
}

/// Generate output path builder method.
#[macro_export]
macro_rules! impl_output_method {
    (options) => {
        /// Set the output file path.
        pub fn output(mut self, path: impl Into<std::path::PathBuf>) -> Self {
            self.options.output = path.into();
            self
        }
    };

    (direct, $field:ident) => {
        /// Set the output file path.
        pub fn output(mut self, path: impl Into<std::path::PathBuf>) -> Self {
            self.$field = Some(path.into());
            self
        }
    };
}

/// Generate linker selection method.
#[macro_export]
macro_rules! impl_linker_method {
    (options) => {
        /// Set the linker to use.
        pub fn linker(mut self, linker: $crate::linker::NativeLinker) -> Self {
            self.options.linker = Some(linker);
            self
        }
    };

    (direct) => {
        /// Set the linker to use.
        pub fn linker(mut self, linker: $crate::linker::NativeLinker) -> Self {
            self.linker = Some(linker);
            self
        }
    };
}

pub use impl_linker_builder_methods;
pub use impl_linker_method;
pub use impl_output_method;

#[cfg(test)]
mod tests {
    #[test]
    fn test_macro_compiles() {
        // Simple compilation test - actual functionality tested through builder modules
        struct TestOptions {
            libraries: Vec<String>,
            library_paths: Vec<std::path::PathBuf>,
        }

        impl TestOptions {
            fn new() -> Self {
                Self {
                    libraries: Vec::new(),
                    library_paths: Vec::new(),
                }
            }

            impl_linker_builder_methods!(direct);
        }

        let opts = TestOptions::new().library("c").library_path("/usr/lib");
        assert_eq!(opts.libraries, vec!["c"]);
        assert_eq!(opts.library_paths, vec![std::path::PathBuf::from("/usr/lib")]);
    }
}
