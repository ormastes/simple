// Modular doctest implementation
//
// This module provides doctest parsing, discovery, and execution functionality.
// The implementation is split across focused modules for maintainability.

pub mod types;
pub mod parser;
pub mod markdown;
pub mod readme_config;
pub mod readme_discovery;
pub mod discovery;
pub mod runner;

// Re-export main types for backward compatibility
pub use types::{DoctestExample, DoctestResult, DoctestStatus, Expected};

// Re-export parser functions
pub use parser::{is_definition_like, parse_doctest_text};

// Re-export markdown functions
pub use markdown::{parse_markdown_doctests, parse_spl_doctests};

// Re-export readme functions and types
pub use readme_config::{parse_readme_config, ParsedReadme, ReadmeConfig, ReadmeLink};
pub use readme_discovery::discover_md_doctests;

// Re-export discovery functions
pub use discovery::discover_doctests;

// Re-export runner functions
pub use runner::{append_to_prelude, build_source, run_examples};
