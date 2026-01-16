//! Locale file generation for i18n
//!
//! This module generates Simple language source files containing
//! i18n string declarations that can be translated.

use super::extractor::ExtractionResult;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::fs;
use std::io;

/// A locale file representation
#[derive(Debug)]
pub struct LocaleFile {
    /// The locale code (e.g., "en-US", "ko-KR")
    pub locale: String,
    /// The strings in this locale, keyed by name
    pub strings: BTreeMap<String, String>,
}

impl LocaleFile {
    /// Create a new locale file
    pub fn new(locale: &str) -> Self {
        Self {
            locale: locale.to_string(),
            strings: BTreeMap::new(),
        }
    }

    /// Add a string to this locale
    pub fn add_string(&mut self, name: &str, text: &str) {
        self.strings.insert(name.to_string(), text.to_string());
    }

    /// Generate the Simple source code for this locale file
    pub fn to_simple_source(&self) -> String {
        let mut output = String::new();

        // Header
        if self.locale == "default" {
            output.push_str("## Auto-generated i18n default strings\n");
            output.push_str("## Do not edit - regenerate using `simple i18n extract`\n\n");
        } else {
            output.push_str(&format!("## {} locale - Translate these strings\n", self.locale));
            output.push_str("## Copy from __init__.spl and translate the values\n\n");
        }

        // String declarations
        for (name, text) in &self.strings {
            // Escape the text for Simple string syntax
            let escaped = escape_simple_string(text);
            output.push_str(&format!("val {} = \"{}\"\n", name, escaped));
        }

        output
    }

    /// Write to a file
    pub fn write_to_file(&self, dir: &Path) -> io::Result<PathBuf> {
        let filename = if self.locale == "default" {
            "__init__.spl".to_string()
        } else {
            format!("__init__.{}.spl", self.locale)
        };

        let path = dir.join(&filename);
        fs::write(&path, self.to_simple_source())?;
        Ok(path)
    }
}

/// Locale file generator
pub struct LocaleGenerator {
    output_dir: PathBuf,
}

impl LocaleGenerator {
    /// Create a new locale generator
    pub fn new(output_dir: PathBuf) -> Self {
        Self { output_dir }
    }

    /// Generate locale files from extraction result
    pub fn generate(&self, result: &ExtractionResult) -> io::Result<Vec<PathBuf>> {
        // Ensure output directory exists
        fs::create_dir_all(&self.output_dir)?;

        // Create the default locale file
        let mut default_locale = LocaleFile::new("default");

        // Sort strings by name for deterministic output
        let mut sorted_strings: Vec<_> = result.strings.iter().collect();
        sorted_strings.sort_by_key(|(name, _)| *name);

        for (name, i18n_string) in sorted_strings {
            default_locale.add_string(name, &i18n_string.default_text);
        }

        // Write the default locale file
        let mut written_files = Vec::new();
        let default_path = default_locale.write_to_file(&self.output_dir)?;
        written_files.push(default_path);

        Ok(written_files)
    }

    /// Generate a template for a new locale
    pub fn generate_locale_template(&self, locale: &str, result: &ExtractionResult) -> io::Result<PathBuf> {
        fs::create_dir_all(&self.output_dir)?;

        let mut locale_file = LocaleFile::new(locale);

        // Sort strings by name for deterministic output
        let mut sorted_strings: Vec<_> = result.strings.iter().collect();
        sorted_strings.sort_by_key(|(name, _)| *name);

        for (name, i18n_string) in sorted_strings {
            // Use the default text as placeholder (translator will replace)
            locale_file.add_string(name, &i18n_string.default_text);
        }

        locale_file.write_to_file(&self.output_dir)
    }
}

/// Escape a string for use in Simple string literals
fn escape_simple_string(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => result.push_str("\\\""),
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            _ => result.push(c),
        }
    }
    result
}

/// Load strings from a locale file
pub fn load_locale_file(path: &Path) -> io::Result<LocaleFile> {
    let content = fs::read_to_string(path)?;
    let locale = extract_locale_from_path(path);
    let mut locale_file = LocaleFile::new(&locale);

    // Parse Simple val declarations
    for line in content.lines() {
        let line = line.trim();
        if line.starts_with("val ") {
            if let Some((name, value)) = parse_val_declaration(line) {
                locale_file.add_string(&name, &value);
            }
        }
    }

    Ok(locale_file)
}

/// Extract locale code from path (e.g., "__init__.ko-KR.spl" -> "ko-KR")
fn extract_locale_from_path(path: &Path) -> String {
    let filename = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
    if filename == "__init__.spl" {
        "default".to_string()
    } else if let Some(stripped) = filename.strip_prefix("__init__.") {
        if let Some(locale) = stripped.strip_suffix(".spl") {
            locale.to_string()
        } else {
            "default".to_string()
        }
    } else {
        "default".to_string()
    }
}

/// Parse a val declaration line
fn parse_val_declaration(line: &str) -> Option<(String, String)> {
    // Simple regex-free parsing for: val name = "value"
    let line = line.strip_prefix("val ")?.trim();

    let eq_pos = line.find('=')?;
    let name = line[..eq_pos].trim().to_string();
    let rest = line[eq_pos + 1..].trim();

    // Extract string value (handle escaped quotes)
    if rest.starts_with('"') && rest.len() > 1 {
        let inner = &rest[1..];
        let mut value = String::new();
        let mut chars = inner.chars().peekable();
        while let Some(c) = chars.next() {
            if c == '\\' {
                if let Some(&next) = chars.peek() {
                    match next {
                        '"' => {
                            value.push('"');
                            chars.next();
                        }
                        '\\' => {
                            value.push('\\');
                            chars.next();
                        }
                        'n' => {
                            value.push('\n');
                            chars.next();
                        }
                        'r' => {
                            value.push('\r');
                            chars.next();
                        }
                        't' => {
                            value.push('\t');
                            chars.next();
                        }
                        _ => value.push(c),
                    }
                }
            } else if c == '"' {
                break;
            } else {
                value.push(c);
            }
        }
        Some((name, value))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_escape_simple_string() {
        assert_eq!(escape_simple_string("hello"), "hello");
        assert_eq!(escape_simple_string("hello \"world\""), "hello \\\"world\\\"");
        assert_eq!(escape_simple_string("line1\nline2"), "line1\\nline2");
    }

    #[test]
    fn test_parse_val_declaration() {
        let (name, value) = parse_val_declaration(r#"val Login_failed_ = "Login failed""#).unwrap();
        assert_eq!(name, "Login_failed_");
        assert_eq!(value, "Login failed");

        let (name, value) = parse_val_declaration(r#"val escaped_ = "with \"quotes\"" "#).unwrap();
        assert_eq!(name, "escaped_");
        assert_eq!(value, "with \"quotes\"");
    }

    #[test]
    fn test_extract_locale_from_path() {
        assert_eq!(
            extract_locale_from_path(Path::new("i18n/__init__.spl")),
            "default"
        );
        assert_eq!(
            extract_locale_from_path(Path::new("i18n/__init__.ko-KR.spl")),
            "ko-KR"
        );
        assert_eq!(
            extract_locale_from_path(Path::new("i18n/__init__.en-US.spl")),
            "en-US"
        );
    }

    #[test]
    fn test_locale_file_to_simple_source() {
        let mut locale = LocaleFile::new("default");
        locale.add_string("Greeting_", "Hello!");
        locale.add_string("Farewell_", "Goodbye!");

        let source = locale.to_simple_source();
        assert!(source.contains("val Farewell_ = \"Goodbye!\""));
        assert!(source.contains("val Greeting_ = \"Hello!\""));
    }
}
