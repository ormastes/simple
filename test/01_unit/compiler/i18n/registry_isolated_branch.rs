pub mod extractor {
    use std::collections::HashMap;

    pub struct I18nString {
        pub name: String,
        pub default_text: String,
        pub template_vars: Vec<String>,
        pub source_file: std::path::PathBuf,
        pub line: usize,
        pub scope: String,
    }

    #[derive(Default)]
    pub struct ExtractionResult {
        pub strings: HashMap<String, I18nString>,
    }
}

#[path = "../../../../src/compiler_rust/compiler/src/i18n/locale.rs"]
pub mod locale;

#[path = "../../../../src/compiler_rust/compiler/src/i18n/registry.rs"]
pub mod registry;

fn main() {}
