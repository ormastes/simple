use std::fs;
use std::path::Path;

use crate::doctest::markdown::{parse_markdown_doctests, parse_spl_doctests};
use crate::doctest::parser::parse_doctest_text;
use crate::doctest::types::DoctestExample;

/// Discover doctest examples from a path:
/// - `.sdt`: parsed directly
/// - `.md`: fenced code blocks
/// - `.spl`, `.simple`, `.sscript`: """ docstring blocks with ```sdoctest fences
/// - directories: walks recursively for all supported formats
pub fn discover_doctests(path: &Path) -> std::io::Result<Vec<DoctestExample>> {
    let mut examples = Vec::new();

    if path.is_dir() {
        for entry in walkdir::WalkDir::new(path) {
            let entry = entry?;
            if entry.file_type().is_file() {
                let p = entry.path();
                let ext = p.extension().and_then(|s| s.to_str());
                match ext {
                    Some("sdt") => examples.extend(parse_doctest_text(&fs::read_to_string(p)?, p)),
                    Some("md") => examples.extend(parse_markdown_doctests(&fs::read_to_string(p)?, p)),
                    Some("spl") | Some("simple") | Some("sscript") => {
                        examples.extend(parse_spl_doctests(&fs::read_to_string(p)?, p))
                    }
                    _ => {}
                }
            }
        }
        return Ok(examples);
    }

    let ext = path.extension().and_then(|s| s.to_str());
    match ext {
        Some("sdt") => examples.extend(parse_doctest_text(&fs::read_to_string(path)?, path)),
        Some("md") => examples.extend(parse_markdown_doctests(&fs::read_to_string(path)?, path)),
        Some("spl") | Some("simple") | Some("sscript") => {
            examples.extend(parse_spl_doctests(&fs::read_to_string(path)?, path))
        }
        _ => {}
    }

    Ok(examples)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::TempDir;

    #[test]
    fn test_discover_sdt_file() {
        let temp_dir = TempDir::new().unwrap();
        let file_path = temp_dir.path().join("test.sdt");
        let mut file = std::fs::File::create(&file_path).unwrap();
        writeln!(file, ">>> x = 5").unwrap();
        writeln!(file, ">>> x").unwrap();
        writeln!(file, "5").unwrap();

        let examples = discover_doctests(&file_path).unwrap();
        // Each >>> line creates a separate example (Python doctest style)
        assert_eq!(examples.len(), 2);
        assert_eq!(examples[0].commands.len(), 1);
        assert_eq!(examples[1].commands.len(), 1);
    }

    #[test]
    fn test_discover_directory() {
        let temp_dir = TempDir::new().unwrap();

        // Create a .sdt file
        let sdt_file = temp_dir.path().join("test.sdt");
        let mut file = std::fs::File::create(&sdt_file).unwrap();
        writeln!(file, ">>> 1 + 1").unwrap();
        writeln!(file, "2").unwrap();

        // Create a .md file
        let md_file = temp_dir.path().join("test.md");
        let mut file = std::fs::File::create(&md_file).unwrap();
        writeln!(file, "```sdoctest").unwrap();
        writeln!(file, ">>> 2 + 2").unwrap();
        writeln!(file, "4").unwrap();
        writeln!(file, "```").unwrap();

        let examples = discover_doctests(temp_dir.path()).unwrap();
        assert_eq!(examples.len(), 2);
    }
}
