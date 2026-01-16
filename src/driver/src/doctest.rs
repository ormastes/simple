use std::fs;
use std::path::{Path, PathBuf};

use std::collections::HashMap;

use crate::interpreter::{Interpreter, RunConfig};

/// Expected outcome for a doctest example.
#[derive(Debug, Clone, PartialEq)]
pub enum Expected {
    Output(String),
    Error(String),
    Empty,
}

/// A single doctest example parsed from a source file.
#[derive(Debug, Clone, PartialEq)]
pub struct DoctestExample {
    pub source: PathBuf,
    pub start_line: usize,
    pub commands: Vec<String>,
    pub expected: Expected,
    /// Section name extracted from nearest markdown heading + sequential number
    /// Example: "Stack Operations #1", "Stack Operations #2"
    pub section_name: Option<String>,
}

/// Result of running a doctest example.
#[derive(Debug, Clone, PartialEq)]
pub struct DoctestResult {
    pub example: DoctestExample,
    pub status: DoctestStatus,
    pub actual: String,
}

#[derive(Debug, Clone, PartialEq)]
pub enum DoctestStatus {
    Passed,
    Failed(String),
}

/// Identify lines that should be treated as definitions/statements rather than expressions.
/// Shared with REPL logic so doctest execution mirrors interactive behavior.
pub fn is_definition_like(line: &str) -> bool {
    let trimmed = line.trim_start();

    if let Some(first) = trimmed.split_whitespace().next() {
        if matches!(
            first,
            "let"
                | "mut"
                | "fn"
                | "struct"
                | "class"
                | "enum"
                | "trait"
                | "impl"
                | "use"
                | "type"
                | "actor"
                | "import"
                | "for"
                | "while"
                | "if"
                | "match"
        ) {
            return true;
        }
    }

    let mut chars = trimmed.char_indices().peekable();
    while let Some((idx, ch)) = chars.next() {
        if ch != '=' {
            continue;
        }
        let prev = trimmed[..idx].chars().rev().find(|c| !c.is_whitespace());
        let next = chars.clone().map(|(_, c)| c).find(|c| !c.is_whitespace());

        let is_comparison = matches!(prev, Some('=') | Some('!') | Some('<') | Some('>')) || matches!(next, Some('='));
        if !is_comparison {
            return true;
        }
    }

    false
}

/// Parse doctest examples from a plain `.sdt`/docstring style string.
pub fn parse_doctest_text(content: &str, source: impl AsRef<Path>) -> Vec<DoctestExample> {
    let mut examples = Vec::new();
    let mut commands: Vec<String> = Vec::new();
    let mut expected: Vec<String> = Vec::new();
    let mut start_line = 0usize;
    let source_path = source.as_ref().to_path_buf();

    let finish_example = |examples: &mut Vec<DoctestExample>,
                          commands: &mut Vec<String>,
                          expected: &mut Vec<String>,
                          start_line: &mut usize| {
        if commands.is_empty() {
            return;
        }

        let expected_kind = if expected.is_empty() {
            Expected::Empty
        } else if let Some(first) = expected.first() {
            if let Some(rest) = first.strip_prefix("Error:") {
                Expected::Error(rest.trim().to_string())
            } else {
                Expected::Output(expected.join("\n"))
            }
        } else {
            Expected::Empty
        };

        examples.push(DoctestExample {
            source: source_path.clone(),
            start_line: *start_line,
            commands: commands.clone(),
            expected: expected_kind,
            section_name: None,
        });

        commands.clear();
        expected.clear();
        *start_line = 0;
    };

    for (idx, raw_line) in content.lines().enumerate() {
        let line_num = idx + 1;
        let line = raw_line.trim_end();

        if let Some(rest) = line.strip_prefix(">>>") {
            if !commands.is_empty() {
                finish_example(&mut examples, &mut commands, &mut expected, &mut start_line);
            }
            start_line = line_num;
            commands.push(rest.trim_start().to_string());
            continue;
        }

        if let Some(rest) = line.strip_prefix("...") {
            // Format is "... " (prompt with space) + indented content, or just "..." + content
            let content = rest.strip_prefix(' ').unwrap_or(rest);
            if let Some(last) = commands.last_mut() {
                last.push('\n');
                last.push_str(content);
            }
            continue;
        }

        if !commands.is_empty() {
            expected.push(line.to_string());
        }
    }

    if !commands.is_empty() {
        finish_example(&mut examples, &mut commands, &mut expected, &mut start_line);
    }

    examples
}

/// Parse doctest examples from Markdown content that uses doctest code fences.
/// Supports both ```sdoctest and ```simple-doctest language hints.
///
/// Extracts section names from nearest markdown headings with sequential numbering.
/// Example: "## Stack Operations" with 2 code blocks yields:
///   - "Stack Operations #1"
///   - "Stack Operations #2"
pub fn parse_markdown_doctests(content: &str, source: impl AsRef<Path>) -> Vec<DoctestExample> {
    let mut examples = Vec::new();
    let mut in_block = false;
    let mut block = String::new();
    let mut block_start_line = 0usize;

    // Section tracking for doctest naming
    let mut current_heading: Option<String> = None;
    let mut section_counts: HashMap<String, usize> = HashMap::new();

    for (idx, line) in content.lines().enumerate() {
        let trimmed = line.trim_start();

        // Track markdown headings (any level: #, ##, ###, etc.)
        if trimmed.starts_with('#') && !in_block {
            let heading_text = trimmed.trim_start_matches('#').trim().to_string();
            if !heading_text.is_empty() {
                current_heading = Some(heading_text);
            }
        }

        // Check for doctest code fence opening with language hint
        if trimmed.starts_with("```sdoctest")
            || trimmed.starts_with("```simple-doctest")
            || trimmed.starts_with("```simple")
        {
            // Only enter block if the hint is for doctests (not other code blocks)
            if trimmed.starts_with("```sdoctest") || trimmed.starts_with("```simple-doctest") {
                in_block = true;
                block.clear();
                block_start_line = idx + 2; // next line after the fence
                continue;
            }
        }

        if trimmed.starts_with("```") && in_block {
            in_block = false;
            let mut block_examples = parse_doctest_text(&block, source.as_ref());

            // Assign section names to examples
            for ex in &mut block_examples {
                ex.start_line += block_start_line;
                if let Some(ref heading) = current_heading {
                    let count = section_counts.entry(heading.clone()).or_insert(0);
                    *count += 1;
                    ex.section_name = Some(format!("{} #{}", heading, count));
                }
            }

            examples.extend(block_examples);
            block.clear();
            continue;
        }

        if in_block {
            block.push_str(line);
            block.push('\n');
        }
    }

    examples
}

/// Parse doctest examples from Simple source files (.spl).
/// Looks for """ docstring blocks with nested ```sdoctest code fences.
/// Example:
/// """
/// Description
/// ```sdoctest
/// >>> code
/// output
/// ```
/// """
pub fn parse_spl_doctests(content: &str, source: impl AsRef<Path>) -> Vec<DoctestExample> {
    let mut examples = Vec::new();
    let mut in_docstring = false;
    let mut docstring = String::new();
    let mut docstring_start_line = 0usize;

    for (idx, line) in content.lines().enumerate() {
        let line_num = idx + 1;
        let trimmed = line.trim_start();

        // Check for docstring opening
        if trimmed.starts_with("\"\"\"") && !in_docstring {
            in_docstring = true;
            docstring.clear();
            docstring_start_line = line_num;

            // Handle inline docstring on same line (e.g., """ content """)
            let rest = &trimmed[3..];
            if rest.contains("\"\"\"") && !rest.trim().is_empty() {
                // Single-line docstring - not supported for now
                in_docstring = false;
            } else {
                docstring.push_str(rest);
                docstring.push('\n');
            }
            continue;
        }

        // Check for docstring closing
        if in_docstring && trimmed.starts_with("\"\"\"") {
            in_docstring = false;

            // Extract code fences from docstring
            let mut block_examples = parse_docstring_fences(&docstring, source.as_ref());
            for ex in &mut block_examples {
                ex.start_line += docstring_start_line;
            }
            examples.extend(block_examples);
            docstring.clear();
            continue;
        }

        if in_docstring {
            docstring.push_str(line);
            docstring.push('\n');
        }
    }

    examples
}

/// Parse code fences from within a docstring.
/// Looks for ```sdoctest and ```simple-doctest fences.
fn parse_docstring_fences(docstring: &str, source: impl AsRef<Path>) -> Vec<DoctestExample> {
    let mut examples = Vec::new();
    let mut in_fence = false;
    let mut fence_content = String::new();
    let mut fence_start_line = 0usize;

    for (idx, line) in docstring.lines().enumerate() {
        let line_num = idx + 1;
        let trimmed = line.trim_start();

        // Check for code fence opening
        if (trimmed.starts_with("```sdoctest") || trimmed.starts_with("```simple-doctest")) && !in_fence {
            in_fence = true;
            fence_content.clear();
            fence_start_line = line_num;
            continue;
        }

        // Check for code fence closing
        if trimmed.starts_with("```") && in_fence {
            in_fence = false;

            // Parse examples from fence content
            let mut fence_examples = parse_doctest_text(&fence_content, source.as_ref());
            for ex in &mut fence_examples {
                ex.start_line += fence_start_line;
            }
            examples.extend(fence_examples);
            fence_content.clear();
            continue;
        }

        if in_fence {
            fence_content.push_str(line);
            fence_content.push('\n');
        }
    }

    examples
}

// ============================================================================
// README.md-based Doctest Discovery (doc/spec/doctest_readme.md)
// ============================================================================

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
fn parse_md_link(line: &str) -> Option<ReadmeLink> {
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
fn is_excluded(path: &Path, excludes: &[String]) -> bool {
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
fn discover_from_readme(readme_path: &Path, parent_config: &ReadmeConfig) -> std::io::Result<Vec<DoctestExample>> {
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
fn extract_md_code_blocks(content: &str, source: &Path, config: &ReadmeConfig) -> Vec<DoctestExample> {
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

// ============================================================================
// Original Discovery Functions
// ============================================================================

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

/// Run doctest examples and return results.
pub fn run_examples(examples: &[DoctestExample]) -> Vec<DoctestResult> {
    let mut results = Vec::new();
    let mut states: HashMap<PathBuf, EvalState> = HashMap::new();

    for example in examples {
        let state = states.entry(example.source.clone()).or_insert_with(|| EvalState {
            prelude: String::new(),
            interpreter: Interpreter::new_no_gc(),
        });
        results.push(run_example(example, state));
    }

    results
}

struct EvalState {
    prelude: String,
    interpreter: Interpreter,
}

fn run_example(example: &DoctestExample, state: &mut EvalState) -> DoctestResult {
    let mut outputs: Vec<String> = Vec::new();
    let mut halted = false;

    let config = RunConfig {
        in_memory: true,
        capture_output: true,
        ..Default::default()
    };

    for command in &example.commands {
        let is_def = is_definition_like(command);
        let source = build_source(&state.prelude, command, is_def);

        match state.interpreter.run(&source, config.clone()) {
            Ok(result) => {
                if is_def {
                    append_to_prelude(&mut state.prelude, command, true);
                }

                let stdout = result.stdout.trim_end();
                if !stdout.is_empty() {
                    outputs.push(stdout.to_string());
                } else if !is_def {
                    outputs.push(result.exit_code.to_string());
                }
            }
            Err(err) => {
                outputs.push(format!("Error: {err}"));
                halted = true;
            }
        }
        if halted {
            break;
        }
    }

    let actual = outputs.join("\n");

    let status = match match_matches(&actual, &example.expected) {
        Ok(()) => DoctestStatus::Passed,
        Err(msg) => DoctestStatus::Failed(msg),
    };

    DoctestResult {
        example: example.clone(),
        status,
        actual,
    }
}

pub fn build_source(prelude: &str, snippet: &str, is_def: bool) -> String {
    let mut src = String::new();
    if !prelude.is_empty() {
        src.push_str(prelude);
        if !prelude.ends_with('\n') {
            src.push('\n');
        }
    }

    if is_def {
        src.push_str(snippet);
        src.push('\n');
        if snippet.trim_end().ends_with(':') {
            src.push_str("    0\n");
        }
        // Add trailing newline for control flow statements that may have print side effects
        // (if, while, for, match blocks)
        let first_word = snippet.trim_start().split_whitespace().next().unwrap_or("");
        if matches!(first_word, "if" | "while" | "for" | "match") {
            src.push_str("print \"\\n\"\n");
        }
        src.push_str("main = 0\n");
    } else {
        let trimmed = snippet.trim_start();
        if trimmed.starts_with("print ") {
            src.push_str(snippet);
            src.push('\n');
            src.push_str("print \"\\n\"\n");
            src.push_str("main = 0\n");
        } else {
            // Store result and only print value if not nil (like Python REPL)
            // But always print newline to separate outputs
            src.push_str("let __repl_val = ");
            src.push_str(snippet);
            src.push('\n');
            src.push_str("if __repl_val != nil:\n");
            src.push_str("    print __repl_val\n");
            src.push_str("print \"\\n\"\n");
            src.push_str("main = 0\n");
        }
    }
    src
}

/// Check if a snippet contains an assignment expression
fn contains_assignment(snippet: &str) -> bool {
    // Simple heuristic: look for '=' that's not part of '==', '!=', '<=', '>='
    let chars: Vec<char> = snippet.chars().collect();
    for i in 0..chars.len() {
        if chars[i] == '=' {
            // Check if it's part of a comparison operator
            let before = if i > 0 { chars[i - 1] } else { ' ' };
            let after = if i + 1 < chars.len() { chars[i + 1] } else { ' ' };
            if before != '=' && before != '!' && before != '<' && before != '>' && after != '=' {
                return true;
            }
        }
    }
    false
}

/// Check if a snippet is a true definition that should be saved in prelude.
/// Control flow statements (if, while, for, match) should NOT be added to prelude
/// because they execute with side effects and shouldn't be re-run on each subsequent input.
fn is_prelude_definition(snippet: &str) -> bool {
    let trimmed = snippet.trim_start();

    // Check keyword-based definitions
    if let Some(first) = trimmed.split_whitespace().next() {
        // Only add actual definitions, not control flow
        if matches!(
            first,
            "let" | "mut" | "fn" | "struct" | "class" | "enum" | "trait" | "impl" | "use" | "type" | "actor" | "import"
        ) {
            return true;
        }
    }

    // Check for assignment (e.g., "a = 1") - need to save variable bindings
    contains_assignment(snippet)
}

pub fn append_to_prelude(prelude: &mut String, snippet: &str, is_def: bool) {
    if !is_def {
        return;
    }
    // Only add true definitions to prelude, not control flow statements
    if !is_prelude_definition(snippet) {
        return;
    }
    prelude.push_str(snippet);
    prelude.push('\n');
    if snippet.trim_end().ends_with(':') {
        prelude.push_str("    0\n");
    }
}

fn match_matches(actual: &str, expected: &Expected) -> Result<(), String> {
    match expected {
        Expected::Empty => {
            if actual.trim().is_empty() {
                Ok(())
            } else {
                Err(format!("Expected no output, got: {actual}"))
            }
        }
        Expected::Output(pattern) => {
            if wildcard_match(actual.trim(), pattern.trim()) {
                Ok(())
            } else {
                Err(format!("Output mismatch:\n  Expected: {pattern}\n  Got: {actual}"))
            }
        }
        Expected::Error(pattern) => {
            if actual.starts_with("Error:") && actual.contains(pattern) {
                Ok(())
            } else {
                Err(format!("Expected error containing '{pattern}', got: {actual}"))
            }
        }
    }
}

fn wildcard_match(text: &str, pattern: &str) -> bool {
    wildcard_match_impl(text.as_bytes(), pattern.as_bytes(), 0, 0)
}

fn wildcard_match_impl(text: &[u8], pattern: &[u8], ti: usize, pi: usize) -> bool {
    if pi == pattern.len() {
        return ti == text.len();
    }
    if ti == text.len() {
        return pattern[pi..].iter().all(|&b| b == b'*');
    }

    let pc = pattern[pi];
    let tc = text[ti];

    if pc == b'*' {
        wildcard_match_impl(text, pattern, ti, pi + 1) || wildcard_match_impl(text, pattern, ti + 1, pi)
    } else if pc == b'.' || pc == tc {
        wildcard_match_impl(text, pattern, ti + 1, pi + 1)
    } else {
        false
    }
}
