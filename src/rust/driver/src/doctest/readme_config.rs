use std::path::Path;

/// Configuration parsed from README.md front matter
#[derive(Debug, Clone, Default)]
pub struct ReadmeConfig {
    /// Patterns to exclude from doctest discovery
    pub excludes: Vec<String>,
    /// Default language for untagged code blocks
    pub lang: String,
    /// Timeout in milliseconds per doctest
    pub timeout: u64,
    /// Whether doctests are disabled in this scope
    pub disabled: bool,
}

impl ReadmeConfig {
    pub fn new() -> Self {
        Self {
            excludes: Vec::new(),
            lang: "simple".to_string(),
            timeout: 5000,
            disabled: false,
        }
    }

    /// Merge with parent config (child overrides parent)
    pub fn merge_with(&self, parent: &ReadmeConfig) -> ReadmeConfig {
        let mut excludes = parent.excludes.clone();
        excludes.extend(self.excludes.clone());

        ReadmeConfig {
            excludes,
            lang: if self.lang != "simple" {
                self.lang.clone()
            } else {
                parent.lang.clone()
            },
            timeout: if self.timeout != 5000 {
                self.timeout
            } else {
                parent.timeout
            },
            disabled: self.disabled || parent.disabled,
        }
    }
}

/// Link extracted from ## Subdirectory or ## Files section
#[derive(Debug, Clone)]
pub struct ReadmeLink {
    pub name: String,
    pub path: String,
    pub is_dir: bool,
}

/// Parsed README.md result
#[derive(Debug, Clone)]
pub struct ParsedReadme {
    pub config: ReadmeConfig,
    pub subdirs: Vec<ReadmeLink>,
    pub files: Vec<ReadmeLink>,
    pub content: String,
}

/// Parse README.md for doctest configuration
pub fn parse_readme_config(content: &str) -> ParsedReadme {
    let mut config = ReadmeConfig::new();
    let mut subdirs = Vec::new();
    let mut files = Vec::new();
    let lines: Vec<&str> = content.lines().collect();
    let mut i = 0;
    let mut content_start = 0;

    // Phase 1: Parse front matter (exclude and config blocks)
    while i < lines.len() {
        let line = lines[i].trim();

        // Parse <!--doctest:exclude block
        if line.starts_with("<!--doctest:exclude") {
            i += 1;
            while i < lines.len() && !lines[i].trim().starts_with("-->") {
                let exclude_line = lines[i].trim();
                if !exclude_line.is_empty() && !exclude_line.starts_with('#') {
                    config.excludes.push(exclude_line.to_string());
                }
                i += 1;
            }
            i += 1;
            continue;
        }

        // Parse <!--doctest:config block
        if line.starts_with("<!--doctest:config") {
            i += 1;
            while i < lines.len() && !lines[i].trim().starts_with("-->") {
                let config_line = lines[i].trim();
                if let Some(pos) = config_line.find(':') {
                    let key = config_line[..pos].trim();
                    let value = config_line[pos + 1..].trim();

                    match key {
                        "lang" => config.lang = value.to_string(),
                        "timeout" => config.timeout = value.parse().unwrap_or(5000),
                        "disabled" => config.disabled = value == "true",
                        _ => {}
                    }
                }
                i += 1;
            }
            i += 1;
            continue;
        }

        // Shorthand: <!--doctest:lang simple-->
        if line.starts_with("<!--doctest:") && line.ends_with("-->") {
            let inner = &line[12..line.len() - 3].trim();
            if inner.starts_with("lang ") {
                config.lang = inner[5..].trim().to_string();
            } else if inner.starts_with("timeout ") {
                config.timeout = inner[8..].trim().parse().unwrap_or(5000);
            } else if *inner == "disabled" {
                config.disabled = true;
            }
            i += 1;
            continue;
        }

        // Not front matter - start of content
        if !line.is_empty() && !line.starts_with("<!--") {
            content_start = i;
            break;
        }

        i += 1;
    }

    // Phase 2: Parse ## Subdirectory and ## Files sections
    let mut current_section = "";

    while i < lines.len() {
        let line = lines[i];
        let trimmed = line.trim();

        // Check for section headers
        if trimmed == "## Subdirectory" || trimmed == "## Subdirectories" {
            current_section = "subdirs";
            i += 1;
            continue;
        }

        if trimmed == "## Files" || trimmed == "## File" {
            current_section = "files";
            i += 1;
            continue;
        }

        // Check for section termination
        if trimmed == "---" {
            break;
        }

        if trimmed.starts_with("## ") && !current_section.is_empty() {
            // New section that's not Subdirectory or Files - stop parsing
            break;
        }

        // Parse links in current section
        if !current_section.is_empty() && trimmed.starts_with("- [") {
            if let Some(link) = parse_md_link(trimmed) {
                // Skip external URLs and anchors
                if !link.path.starts_with("http") && !link.path.starts_with('#') {
                    if current_section == "subdirs" {
                        subdirs.push(link);
                    } else if current_section == "files" {
                        files.push(link);
                    }
                }
            }
        }

        i += 1;
    }

    // Build content after front matter
    let content_lines: Vec<&str> = lines[content_start..].to_vec();

    ParsedReadme {
        config,
        subdirs,
        files,
        content: content_lines.join("\n"),
    }
}

/// Parse a markdown link: - [Text](path)
pub(crate) fn parse_md_link(line: &str) -> Option<ReadmeLink> {
    let trimmed = line.trim();

    // Find [
    let bracket_start = trimmed.find('[')?;
    // Find ]
    let bracket_end = trimmed[bracket_start..].find(']')? + bracket_start;
    // Find (
    let paren_start = trimmed[bracket_end..].find('(')? + bracket_end;
    // Find )
    let paren_end = trimmed[paren_start..].find(')')? + paren_start;

    let text = &trimmed[bracket_start + 1..bracket_end];
    let href = &trimmed[paren_start + 1..paren_end];

    Some(ReadmeLink {
        name: text.to_string(),
        path: href.trim_end_matches('/').to_string(),
        is_dir: href.ends_with('/'),
    })
}

/// Check if path matches any exclude pattern
pub fn is_excluded(path: &Path, excludes: &[String]) -> bool {
    let path_str = path.to_string_lossy();

    for pattern in excludes {
        // Handle negation
        if pattern.starts_with('!') {
            continue;
        }

        // Simple pattern matching
        let clean_pattern = pattern
            .trim_start_matches("**/")
            .trim_end_matches("/**")
            .replace("**", "");

        if clean_pattern.contains('*') {
            // Wildcard - check parts
            for part in clean_pattern.split('*') {
                if !part.is_empty() && !path_str.contains(part) {
                    continue;
                }
            }
            return true;
        } else if path_str.contains(&clean_pattern) || path_str.ends_with(&clean_pattern) {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_readme_config_new() {
        let config = ReadmeConfig::new();
        assert_eq!(config.lang, "simple");
        assert_eq!(config.timeout, 5000);
        assert!(!config.disabled);
        assert!(config.excludes.is_empty());
    }

    #[test]
    fn test_readme_config_merge() {
        let parent = ReadmeConfig {
            excludes: vec!["test".to_string()],
            lang: "rust".to_string(),
            timeout: 3000,
            disabled: false,
        };

        let child = ReadmeConfig {
            excludes: vec!["foo".to_string()],
            lang: "simple".to_string(),
            timeout: 5000,
            disabled: true,
        };

        let merged = child.merge_with(&parent);
        assert_eq!(merged.excludes.len(), 2);
        assert_eq!(merged.lang, "rust");
        assert_eq!(merged.timeout, 3000);
        assert!(merged.disabled);
    }

    #[test]
    fn test_parse_md_link() {
        let link = parse_md_link("- [Test](path/to/file.md)").unwrap();
        assert_eq!(link.name, "Test");
        assert_eq!(link.path, "path/to/file.md");
        assert!(!link.is_dir);

        let dir_link = parse_md_link("- [Dir](path/to/dir/)").unwrap();
        assert!(dir_link.is_dir);
    }

    #[test]
    fn test_is_excluded() {
        let excludes = vec!["test".to_string(), "**/node_modules/**".to_string()];
        assert!(is_excluded(Path::new("test/file.md"), &excludes));
        assert!(is_excluded(Path::new("node_modules/pkg"), &excludes));
        assert!(!is_excluded(Path::new("src/file.md"), &excludes));
    }
}
