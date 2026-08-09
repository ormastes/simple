use std::fs;
use std::path::Path;

use crate::doctest::readme_config::{is_excluded, parse_readme_config, ParsedReadme, ReadmeConfig};
use crate::doctest::types::{DoctestExample, Expected};

/// Discover doctests from markdown using README.md hierarchy
///
/// Starts from root_path, looks for README.md, and follows
/// ## Subdirectory and ## Files links.
pub fn discover_md_doctests(root_path: &Path) -> std::io::Result<Vec<DoctestExample>> {
    let mut examples = Vec::new();

    if root_path.is_file() {
        if root_path.extension().and_then(|s| s.to_str()) == Some("md") {
            let content = fs::read_to_string(root_path)?;
            let parsed = parse_readme_config(&content);
            examples.extend(extract_md_code_blocks(&parsed.content, root_path, &parsed.config));
        }
        return Ok(examples);
    }

    let readme_path = root_path.join("README.md");
    if readme_path.exists() {
        examples.extend(discover_from_readme(&readme_path, &ReadmeConfig::new())?);
    }

    Ok(examples)
}

/// Discover doctests from a README.md and its linked files
pub(crate) fn discover_from_readme(
    readme_path: &Path,
    parent_config: &ReadmeConfig,
) -> std::io::Result<Vec<DoctestExample>> {
    let mut examples = Vec::new();

    if !readme_path.exists() {
        return Ok(examples);
    }

    let content = fs::read_to_string(readme_path)?;
    let parsed = parse_readme_config(&content);
    let config = parsed.config.merge_with(parent_config);

    if config.disabled {
        return Ok(examples);
    }

    let base_dir = readme_path.parent().unwrap_or(Path::new("."));

    // Add the README.md itself if it has code blocks
    let readme_examples = extract_md_code_blocks(&parsed.content, readme_path, &config);
    examples.extend(readme_examples);

    // Process subdirectories
    for subdir_link in &parsed.subdirs {
        let subdir_path = base_dir.join(&subdir_link.path);

        if is_excluded(&subdir_path, &config.excludes) {
            continue;
        }

        let subdir_readme = subdir_path.join("README.md");
        if subdir_readme.exists() {
            examples.extend(discover_from_readme(&subdir_readme, &config)?);
        }
    }

    // Process linked files
    for file_link in &parsed.files {
        let file_path = base_dir.join(&file_link.path);

        if is_excluded(&file_path, &config.excludes) {
            continue;
        }

        if !file_path.exists() {
            continue;
        }

        let file_content = fs::read_to_string(&file_path)?;
        let file_parsed = parse_readme_config(&file_content);
        let file_config = file_parsed.config.merge_with(&config);

        if file_config.disabled {
            continue;
        }

        let file_examples = extract_md_code_blocks(&file_parsed.content, &file_path, &file_config);
        examples.extend(file_examples);
    }

    Ok(examples)
}

/// Extract code blocks from markdown content that should be tested
pub(crate) fn extract_md_code_blocks(content: &str, source: &Path, config: &ReadmeConfig) -> Vec<DoctestExample> {
    let mut examples = Vec::new();
    let mut in_block = false;
    let mut block_lines: Vec<String> = Vec::new();
    let mut block_start_line = 0;
    let mut block_lang = String::new();
    let mut block_skip = false;

    for (idx, line) in content.lines().enumerate() {
        let trimmed = line.trim();

        if trimmed.starts_with("```") && !in_block {
            in_block = true;
            block_lines.clear();
            block_start_line = idx + 2; // Line after fence

            // Parse language and modifiers
            let lang_part = &trimmed[3..];
            block_skip = false;

            if lang_part.is_empty() {
                // No tag - use default language
                block_lang = config.lang.clone();
            } else if lang_part.contains(":skip") {
                block_skip = true;
                block_lang = lang_part.split(':').next().unwrap_or("").to_string();
            } else if lang_part.contains(':') {
                block_lang = lang_part.split(':').next().unwrap_or("").to_string();
            } else {
                block_lang = lang_part.to_string();
            }

            continue;
        }

        if trimmed.starts_with("```") && in_block {
            in_block = false;

            // Only process Simple code blocks
            if !block_skip && (block_lang == "simple" || block_lang == config.lang || block_lang.is_empty()) {
                let code = block_lines.join("\n");

                // Check for doctest marker or assertions
                if code.contains("# doctest") || code.contains("assert ") || code.contains("assert(") {
                    // Convert to DoctestExample
                    let commands = extract_commands_from_block(&code);
                    if !commands.is_empty() {
                        examples.push(DoctestExample {
                            source: source.to_path_buf(),
                            start_line: block_start_line,
                            commands,
                            expected: Expected::Empty, // Assertions handle their own checks
                            section_name: None,
                        });
                    }
                }
            }

            block_lines.clear();
            continue;
        }

        if in_block {
            block_lines.push(line.to_string());
        }
    }

    examples
}

/// Extract executable commands from a code block
fn extract_commands_from_block(code: &str) -> Vec<String> {
    let mut commands = Vec::new();
    let mut in_doctest = false;
    let mut current_command = String::new();

    for line in code.lines() {
        let trimmed = line.trim();

        if trimmed == "# doctest" || trimmed == "#doctest" {
            in_doctest = true;
            // Add everything before # doctest as setup
            if !current_command.is_empty() {
                commands.push(current_command.trim().to_string());
                current_command.clear();
            }
            continue;
        }

        if in_doctest {
            // After # doctest marker - these are the actual test commands
            if !trimmed.is_empty() && !trimmed.starts_with('#') {
                current_command.push_str(line);
                current_command.push('\n');
            }
        } else {
            // Before # doctest marker - this is setup code
            current_command.push_str(line);
            current_command.push('\n');
        }
    }

    if !current_command.is_empty() {
        commands.push(current_command.trim().to_string());
    }

    // If no # doctest marker, treat entire block as one command
    if commands.len() == 1 && !code.contains("# doctest") {
        return vec![code.to_string()];
    }

    commands
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_commands_from_block() {
        let code = r#"let x = 5
# doctest
assert x == 5"#;
        let commands = extract_commands_from_block(code);
        assert_eq!(commands.len(), 2);
        assert_eq!(commands[0], "let x = 5");
        assert_eq!(commands[1], "assert x == 5");
    }

    #[test]
    fn test_extract_commands_no_marker() {
        let code = "let x = 5\nassert x == 5";
        let commands = extract_commands_from_block(code);
        assert_eq!(commands.len(), 1);
        assert_eq!(commands[0], code);
    }
}
