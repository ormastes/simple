//! Generate individual feature documentation files

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

use chrono::Local;

use super::types::SspecDoc;

/// Generate documentation for a single feature
pub fn generate_feature_doc(sspec_doc: &SspecDoc, output_dir: &Path) -> Result<(), Box<dyn std::error::Error>> {
    let file_name = output_stem(sspec_doc);

    let feature_name = preferred_feature_name(sspec_doc, &file_name);

    let mut md = String::new();

    md.push_str(&format!("# {}\n\n", feature_name));
    if let Some(summary) = extract_summary(sspec_doc) {
        md.push_str(&format!("{}\n\n", summary));
    }

    let metadata_rows = build_metadata_rows(sspec_doc);
    if !metadata_rows.is_empty() {
        md.push_str("## At a Glance\n\n");
        md.push_str("| Field | Value |\n");
        md.push_str("|-------|-------|\n");
        for (field, value) in metadata_rows {
            md.push_str(&format!(
                "| {} | {} |\n",
                escape_table_cell(&field),
                escape_table_cell(&value)
            ));
        }
        md.push('\n');
    }

    let scenarios = extract_scenarios(&sspec_doc.raw_content);
    if !scenarios.is_empty() {
        md.push_str("## Scenario Summary\n\n");
        md.push_str("| Metric | Count |\n");
        md.push_str("|--------|------:|\n");
        md.push_str(&format!("| Total scenarios | {} |\n", scenarios.len()));
        md.push_str(&format!(
            "| Active scenarios | {} |\n",
            scenarios
                .iter()
                .filter(|s| matches!(s.kind, ScenarioKind::Normal | ScenarioKind::Slow))
                .count()
        ));
        md.push_str(&format!(
            "| Slow scenarios | {} |\n",
            scenarios.iter().filter(|s| s.kind == ScenarioKind::Slow).count()
        ));
        md.push_str(&format!(
            "| Skipped scenarios | {} |\n",
            scenarios.iter().filter(|s| s.kind == ScenarioKind::Skipped).count()
        ));
        md.push_str(&format!(
            "| Pending scenarios | {} |\n",
            scenarios.iter().filter(|s| s.kind == ScenarioKind::Pending).count()
        ));
        md.push('\n');
    }

    let body = render_doc_body(sspec_doc);
    if !body.is_empty() {
        md.push_str(&body);
        md.push_str("\n\n");
    } else {
        md.push_str("## Overview\n\n");
        md.push_str("Documentation was generated from executable SSpec scenarios.\n\n");
    }

    append_extracted_examples_section(&mut md, sspec_doc);
    append_evidence_section(&mut md, sspec_doc);

    if !scenarios.is_empty() {
        md.push_str("## Scenarios\n\n");
        for scenario in scenarios {
            let prefix = match scenario.kind {
                ScenarioKind::Normal => "-",
                ScenarioKind::Slow => "- [slow]",
                ScenarioKind::Skipped => "- [skip]",
                ScenarioKind::Pending => "- [pending]",
            };
            md.push_str(&format!("{} {}\n", prefix, scenario.name));
        }
        md.push('\n');
    }

    // Related Documentation cross-reference section
    append_related_docs_section(&mut md, sspec_doc);

    let output_path = output_dir.join(format!("{}.md", file_name));
    let mut file = fs::File::create(output_path)?;
    file.write_all(md.trim_end().as_bytes())?;
    file.write_all(b"\n")?;

    Ok(())
}

fn humanize_filename(stem: &str) -> String {
    let base = stem.strip_suffix("_spec").unwrap_or(stem);
    let words: Vec<String> = base
        .split('_')
        .filter(|w| !w.is_empty())
        .map(|word| {
            let mut chars = word.chars();
            match chars.next() {
                Some(first) => format!("{}{}", first.to_ascii_uppercase(), chars.as_str()),
                None => String::new(),
            }
        })
        .collect();

    if words.is_empty() {
        "Specification".to_string()
    } else {
        format!("{} Specification", words.join(" "))
    }
}

fn build_metadata_rows(sspec_doc: &SspecDoc) -> Vec<(String, String)> {
    let mut rows = Vec::new();

    if let Some(id) = sspec_doc
        .metadata
        .id
        .clone()
        .or_else(|| (!sspec_doc.feature_ids.is_empty()).then(|| sspec_doc.feature_ids.join(", ")))
    {
        rows.push(("Feature IDs".to_string(), id));
    }
    if let Some(category) = &sspec_doc.metadata.category {
        rows.push(("Category".to_string(), category.clone()));
    }
    if let Some(difficulty) = &sspec_doc.metadata.difficulty {
        rows.push(("Difficulty".to_string(), difficulty.clone()));
    }
    if let Some(status) = &sspec_doc.metadata.status {
        rows.push(("Status".to_string(), status.clone()));
    }
    if let Some(doc_type) = &sspec_doc.metadata.doc_type {
        rows.push(("Type".to_string(), doc_type.clone()));
    }
    if let Some(source_doc) = &sspec_doc.metadata.source_doc {
        rows.push(("Reference".to_string(), source_doc.clone()));
    }
    if let Some(requirements) = &sspec_doc.metadata.requirements {
        rows.push(("Requirements".to_string(), requirements.clone()));
    }
    if let Some(plan) = &sspec_doc.metadata.plan {
        rows.push(("Plan".to_string(), plan.clone()));
    }
    if let Some(design) = &sspec_doc.metadata.design {
        rows.push(("Design".to_string(), design.clone()));
    }
    if let Some(research) = &sspec_doc.metadata.research {
        rows.push(("Research".to_string(), research.clone()));
    }
    if !sspec_doc.metadata.related.is_empty() {
        rows.push(("Related".to_string(), sspec_doc.metadata.related.join(", ")));
    }
    if !sspec_doc.metadata.dependencies.is_empty() {
        rows.push(("Dependencies".to_string(), sspec_doc.metadata.dependencies.join(", ")));
    }
    rows.push(("Source".to_string(), format!("`{}`", sspec_doc.file_path.display())));
    rows.push(("Updated".to_string(), Local::now().format("%Y-%m-%d").to_string()));
    rows.push(("Generator".to_string(), "`simple sspec-docgen` (Rust)".to_string()));

    rows
}

fn strip_header_metadata(content: &str) -> String {
    let mut out = Vec::new();
    let mut skipping_leading_blanks = true;
    let mut skipping_metadata_list = false;

    for line in content.lines() {
        let trimmed = line.trim();
        let is_metadata = trimmed.starts_with("**Feature ID:**")
            || trimmed.starts_with("**Feature IDs:**")
            || trimmed.starts_with("**Category:**")
            || trimmed.starts_with("**Difficulty:**")
            || trimmed.starts_with("**Status:**")
            || trimmed.starts_with("**Source:**")
            || trimmed.starts_with("**Type:**")
            || trimmed.starts_with("**Requirements:**")
            || trimmed.starts_with("**Plan:**")
            || trimmed.starts_with("**Design:**")
            || trimmed.starts_with("**Research:**")
            || trimmed.starts_with("**Related:**")
            || trimmed.starts_with("**Dependencies:**")
            || trimmed.starts_with("**Artifacts:**")
            || trimmed.starts_with("**Screenshots:**")
            || trimmed.starts_with("**TUI Captures:**")
            || trimmed.starts_with("**Logs:**");

        if trimmed.starts_with("# ") || is_metadata {
            skipping_metadata_list = is_metadata;
            continue;
        }

        if skipping_metadata_list {
            if trimmed.starts_with("- ") || trimmed.starts_with("* ") {
                continue;
            }
            if trimmed.is_empty() {
                continue;
            }
            skipping_metadata_list = false;
        }

        if skipping_leading_blanks && trimmed.is_empty() {
            continue;
        }

        skipping_leading_blanks = false;
        out.push(line);
    }

    out.join("\n").trim().to_string()
}

fn render_doc_body(sspec_doc: &SspecDoc) -> String {
    let mut sections = Vec::new();

    if let Some(first_block) = sspec_doc.doc_blocks.first() {
        let first_content = strip_header_metadata(&first_block.content);
        if !first_content.is_empty() {
            sections.push(first_content);
        }

        for doc_block in sspec_doc.doc_blocks.iter().skip(1) {
            let content = doc_block.content.trim();
            if !content.is_empty() {
                sections.push(content.to_string());
            }
        }
    }

    sections.join("\n\n").trim().to_string()
}

pub(crate) fn output_stem(sspec_doc: &SspecDoc) -> String {
    if let Some(source_doc) = &sspec_doc.metadata.source_doc {
        if let Some(stem) = Path::new(source_doc).file_stem().and_then(|s| s.to_str()) {
            if !stem.trim().is_empty() {
                return stem.to_string();
            }
        }
    }

    let stem = sspec_doc
        .file_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("unknown")
        .to_string();

    let path_str = sspec_doc.file_path.to_string_lossy();
    if path_str.contains("/test/specs/") || path_str.contains("\\test\\specs\\") {
        return stem.strip_suffix("_spec").unwrap_or(&stem).to_string();
    }

    stem
}

fn preferred_feature_name(sspec_doc: &SspecDoc, stem: &str) -> String {
    if let Some(title) = &sspec_doc.feature_title {
        let trimmed = title.trim();
        if !trimmed.is_empty()
            && !trimmed.starts_with('-')
            && trimmed != "Test Specification"
            && trimmed != "- Test Specification"
        {
            return trimmed.to_string();
        }
    }

    humanize_filename(stem)
}

fn extract_summary(sspec_doc: &SspecDoc) -> Option<String> {
    let body = render_doc_body(sspec_doc);
    if body.is_empty() {
        return None;
    }

    extract_summary_from_markdown(&body)
}

fn extract_summary_from_markdown(content: &str) -> Option<String> {
    let mut in_overview = false;
    let mut paragraph = Vec::new();

    for line in content.lines() {
        let trimmed = line.trim();

        if trimmed.starts_with("## ") {
            in_overview = trimmed == "## Overview" || trimmed == "## Description";
            if !paragraph.is_empty() {
                break;
            }
            continue;
        }

        if trimmed.starts_with('#') || trimmed.starts_with("```") {
            if !paragraph.is_empty() {
                break;
            }
            continue;
        }

        if is_metadata_line(trimmed) {
            if !paragraph.is_empty() {
                break;
            }
            continue;
        }

        if trimmed.is_empty() {
            if !paragraph.is_empty() {
                break;
            }
            continue;
        }

        if in_overview || paragraph.is_empty() {
            if !trimmed.starts_with("- ") && !trimmed.starts_with("* ") {
                paragraph.push(trimmed.to_string());
            }
        }
    }

    if paragraph.is_empty() {
        None
    } else {
        Some(paragraph.join(" "))
    }
}

fn is_metadata_line(trimmed: &str) -> bool {
    trimmed.starts_with("**") && trimmed.contains(":**")
}

fn append_evidence_section(md: &mut String, sspec_doc: &SspecDoc) {
    let evidence_groups = [
        ("Artifacts", &sspec_doc.metadata.artifacts),
        ("Screenshots", &sspec_doc.metadata.screenshots),
        ("TUI Captures", &sspec_doc.metadata.tui_captures),
        ("Logs", &sspec_doc.metadata.logs),
    ];

    let has_evidence = evidence_groups.iter().any(|(_, items)| !items.is_empty());

    if !has_evidence {
        return;
    }

    md.push_str("## Evidence\n\n");
    append_evidence_summary(md, &evidence_groups);

    for (title, items) in evidence_groups {
        append_evidence_group(md, title, items);
    }
}

fn append_extracted_examples_section(md: &mut String, sspec_doc: &SspecDoc) {
    let examples = extract_examples(&sspec_doc.raw_content);
    if examples.is_empty() {
        return;
    }

    md.push_str("## Example Details\n\n");
    md.push_str("| Example | Kind | Reference |\n");
    md.push_str("|---------|------|-----------|\n");
    for (idx, example) in examples.iter().enumerate() {
        let reference = example.source_hint.clone().unwrap_or_else(|| "—".to_string());
        md.push_str(&format!(
            "| {} | {} | {} |\n",
            idx + 1,
            escape_table_cell(&example.kind),
            escape_table_cell(&reference)
        ));
    }
    md.push('\n');

    for (idx, example) in examples.iter().enumerate() {
        md.push_str(&format!("### {}. {}\n\n", idx + 1, example.title));

        let mut details = Vec::new();
        details.push(format!("Kind: {}", example.kind));
        if let Some(source_hint) = &example.source_hint {
            details.push(format!("Reference: {}", source_hint));
        }
        if let Some(scenario_name) = &example.scenario_name {
            details.push(format!("Scenario: `{}`", scenario_name));
        }
        md.push_str(&format!("*{}*\n\n", details.join(" | ")));

        if !example.description.is_empty() {
            md.push_str(&example.description);
            md.push_str("\n\n");
        }

        if !example.code.is_empty() {
            md.push_str("```simple\n");
            md.push_str(example.code.trim_end());
            md.push_str("\n```\n\n");
        }
    }
}

fn append_evidence_summary(md: &mut String, evidence_groups: &[(&str, &Vec<String>)]) {
    md.push_str("| Category | Count |\n");
    md.push_str("|----------|------:|\n");

    for (title, items) in evidence_groups {
        if items.is_empty() {
            continue;
        }

        md.push_str(&format!("| {} | {} |\n", title, items.len()));
    }

    md.push('\n');
}

fn append_evidence_group(md: &mut String, title: &str, items: &[String]) {
    if items.is_empty() {
        return;
    }

    md.push_str(&format!("### {}\n\n", title));
    md.push_str("| Item | Kind | Path |\n");
    md.push_str("|------|------|------|\n");

    for item in items {
        let item_name = evidence_item_name(item);
        let kind = evidence_item_kind(title, item);
        md.push_str(&format!(
            "| `{}` | {} | `{}` |\n",
            escape_table_cell(&item_name),
            kind,
            escape_table_cell(item)
        ));
    }

    md.push('\n');
}

fn evidence_item_name(item: &str) -> String {
    Path::new(item)
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or(item)
        .to_string()
}

fn evidence_item_kind(group: &str, item: &str) -> String {
    let ext = Path::new(item)
        .extension()
        .and_then(|s| s.to_str())
        .map(|s| s.to_ascii_lowercase());

    match group {
        "Screenshots" => ext
            .map(|ext| format!("{} screenshot", ext.to_uppercase()))
            .unwrap_or_else(|| "Screenshot".to_string()),
        "TUI Captures" => "ANSI capture".to_string(),
        "Logs" => "Log file".to_string(),
        _ => match ext.as_deref() {
            Some("json") => "JSON artifact".to_string(),
            Some("txt") => "Text artifact".to_string(),
            Some("html") => "HTML report".to_string(),
            Some("svg") => "SVG asset".to_string(),
            Some("png") => "PNG artifact".to_string(),
            Some("jpg") | Some("jpeg") => "JPEG artifact".to_string(),
            Some("webp") => "WebP artifact".to_string(),
            Some(other) => format!("{} artifact", other.to_uppercase()),
            None => "Artifact".to_string(),
        },
    }
}

fn append_related_docs_section(md: &mut String, sspec_doc: &SspecDoc) {
    let mut links = Vec::new();

    if let Some(req) = &sspec_doc.metadata.requirements {
        if req != "N/A" && !req.is_empty() {
            links.push(format!("- **Requirements:** [{}]({})", req, req));
        }
    }
    if let Some(plan) = &sspec_doc.metadata.plan {
        if plan != "N/A" && !plan.is_empty() {
            links.push(format!("- **Plan:** [{}]({})", plan, plan));
        }
    }
    if let Some(design) = &sspec_doc.metadata.design {
        if design != "N/A" && !design.is_empty() {
            links.push(format!("- **Design:** [{}]({})", design, design));
        }
    }
    if let Some(research) = &sspec_doc.metadata.research {
        if research != "N/A" && !research.is_empty() {
            links.push(format!("- **Research:** [{}]({})", research, research));
        }
    }

    if !links.is_empty() {
        md.push_str("## Related Documentation\n\n");
        for link in links {
            md.push_str(&link);
            md.push('\n');
        }
        md.push('\n');
    }
}

fn escape_table_cell(value: &str) -> String {
    value.replace('|', "\\|")
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ScenarioKind {
    Normal,
    Slow,
    Skipped,
    Pending,
}

struct Scenario {
    name: String,
    kind: ScenarioKind,
}

struct ExtractedExample {
    title: String,
    source_hint: Option<String>,
    description: String,
    code: String,
    kind: String,
    scenario_name: Option<String>,
}

fn extract_scenarios(content: &str) -> Vec<Scenario> {
    let mut scenarios = Vec::new();

    for line in content.lines() {
        let trimmed = line.trim();
        let (kind, prefix) = if trimmed.starts_with("slow_it ") {
            (ScenarioKind::Slow, "slow_it ")
        } else if trimmed.starts_with("skip_it ") {
            (ScenarioKind::Skipped, "skip_it ")
        } else if trimmed.starts_with("pending ") {
            (ScenarioKind::Pending, "pending ")
        } else if trimmed.starts_with("it ") {
            (ScenarioKind::Normal, "it ")
        } else {
            continue;
        };

        if let Some(name) = extract_quoted_name(trimmed.strip_prefix(prefix).unwrap_or(trimmed)) {
            scenarios.push(Scenario { name, kind });
        }
    }

    scenarios
}

fn extract_quoted_name(input: &str) -> Option<String> {
    let start = input.find('"')?;
    let rest = &input[start + 1..];
    let end = rest.find('"')?;
    Some(rest[..end].to_string())
}

fn extract_examples(content: &str) -> Vec<ExtractedExample> {
    let lines: Vec<&str> = content.lines().collect();
    let mut examples = Vec::new();
    let mut i = 0;

    while i < lines.len() {
        let trimmed = lines[i].trim();
        let Some(header) = trimmed.strip_prefix("## Test:") else {
            i += 1;
            continue;
        };

        let (title, source_hint) = parse_example_heading(header.trim());
        i += 1;

        while i < lines.len() && lines[i].trim().is_empty() {
            i += 1;
        }

        let mut description = String::new();
        if i < lines.len() && lines[i].trim() == "\"\"\"" {
            i += 1;
            let start = i;
            while i < lines.len() && lines[i].trim() != "\"\"\"" {
                i += 1;
            }
            description = lines[start..i].join("\n").trim().to_string();
            if i < lines.len() && lines[i].trim() == "\"\"\"" {
                i += 1;
            }
        }

        while i < lines.len() && lines[i].trim().is_empty() {
            i += 1;
        }

        let code_start = i;
        while i < lines.len() && !lines[i].trim().starts_with("## Test:") {
            i += 1;
        }

        let code = lines[code_start..i].join("\n").trim().to_string();
        let (kind, scenario_name) = classify_example_code(&code);

        examples.push(ExtractedExample {
            title,
            source_hint,
            description,
            code,
            kind,
            scenario_name,
        });
    }

    examples
}

fn parse_example_heading(header: &str) -> (String, Option<String>) {
    if let Some((title, suffix)) = header.rsplit_once(" (") {
        if suffix.ends_with(')') {
            return (
                title.trim().to_string(),
                Some(suffix.trim_end_matches(')').trim().to_string()),
            );
        }
    }

    (header.trim().to_string(), None)
}

fn classify_example_code(code: &str) -> (String, Option<String>) {
    for line in code.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }

        if let Some(name) = trimmed.strip_prefix("it ").and_then(extract_quoted_name) {
            return ("Scenario".to_string(), Some(name));
        }
        if let Some(name) = trimmed.strip_prefix("skip_it ").and_then(extract_quoted_name) {
            return ("Skipped scenario".to_string(), Some(name));
        }
        if let Some(name) = trimmed.strip_prefix("slow_it ").and_then(extract_quoted_name) {
            return ("Slow scenario".to_string(), Some(name));
        }
        if let Some(name) = trimmed.strip_prefix("pending ").and_then(extract_quoted_name) {
            return ("Pending scenario".to_string(), Some(name));
        }
        if let Some(rest) = trimmed.strip_prefix("fn ") {
            let name = rest
                .split(['(', ' ', ':'])
                .next()
                .unwrap_or("example")
                .trim()
                .to_string();
            return ("Function example".to_string(), Some(name));
        }
        if let Some(rest) = trimmed.strip_prefix("class ") {
            let name = rest
                .split(['(', ' ', ':'])
                .next()
                .unwrap_or("example")
                .trim()
                .to_string();
            return ("Class example".to_string(), Some(name));
        }
        if trimmed.starts_with("describe ") {
            return ("Describe block".to_string(), extract_quoted_name(trimmed));
        }
        return ("Code example".to_string(), None);
    }

    ("Code example".to_string(), None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::types::FeatureMetadata;
    use std::fs;

    use tempfile::tempdir;

    #[test]
    fn test_generate_feature_doc_renders_evidence_tables() {
        let tempdir = tempdir().expect("tempdir");
        let doc = SspecDoc {
            file_path: PathBuf::from("test/app/web_dashboard/tmux_rest_api_spec.spl"),
            raw_content: String::new(),
            doc_blocks: vec![],
            feature_title: Some("Evidence Rendering".to_string()),
            feature_ids: vec![],
            metadata: FeatureMetadata {
                artifacts: vec![
                    "build/test-artifacts/app/web_dashboard/tmux_rest_api/result.json".to_string(),
                    "build/test-artifacts/app/web_dashboard/tmux_rest_api/notes.txt".to_string(),
                ],
                screenshots: vec!["doc/spec/image/app/web_dashboard/tmux_rest_api/shot.png".to_string()],
                tui_captures: vec!["build/test-artifacts/app/web_dashboard/tmux_rest_api/terminal.ansi".to_string()],
                logs: vec!["build/test-artifacts/app/web_dashboard/tmux_rest_api/run.log".to_string()],
                ..Default::default()
            },
        };

        generate_feature_doc(&doc, tempdir.path()).expect("generate doc");

        let output = fs::read_to_string(tempdir.path().join("tmux_rest_api_spec.md")).expect("read doc");

        assert!(output.contains("## Evidence"));
        assert!(output.contains("| Category | Count |"));
        assert!(output.contains("### Artifacts"));
        assert!(output.contains("| Item | Kind | Path |"));
        assert!(output.contains("JSON artifact"));
        assert!(output.contains("Text artifact"));
        assert!(output.contains("ANSI capture"));
        assert!(output.contains("Log file"));
    }

    #[test]
    fn test_generate_feature_doc_title_first_and_summary_table() {
        let tempdir = tempdir().expect("tempdir");
        let doc = SspecDoc {
            file_path: PathBuf::from("test/feature/app/example_spec.spl"),
            raw_content: r#"
it "renders docs":
    expect(true).to_equal(true)
skip_it "skips cleanly":
    expect(true).to_equal(true)
"#
            .to_string(),
            doc_blocks: vec![super::super::types::DocBlock {
                content: r#"
# Example Spec

**Feature IDs:** #EX-001
**Category:** Tooling
**Status:** Implemented

## Overview

This page should start with the title and a plain-language summary.

## Examples

```simple
expect(true).to_equal(true)
```
"#
                .trim()
                .to_string(),
                line_start: 0,
                line_end: 16,
            }],
            feature_title: Some("Example Spec".to_string()),
            feature_ids: vec![],
            metadata: FeatureMetadata {
                category: Some("Tooling".to_string()),
                status: Some("Implemented".to_string()),
                ..Default::default()
            },
        };

        generate_feature_doc(&doc, tempdir.path()).expect("generate doc");

        let output = fs::read_to_string(tempdir.path().join("example_spec.md")).expect("read doc");
        let lines: Vec<_> = output.lines().collect();

        assert_eq!(lines.first().copied(), Some("# Example Spec"));
        assert!(output.contains("This page should start with the title and a plain-language summary."));
        assert!(output.contains("## At a Glance"));
        assert!(output.contains("| Source | `test/feature/app/example_spec.spl` |"));
        assert!(output.contains("| Generator | `simple sspec-docgen` (Rust) |"));
        assert!(output.contains("## Scenario Summary"));
        assert!(output.contains("| Active scenarios | 1 |"));
        assert!(output.contains("| Skipped scenarios | 1 |"));
    }

    #[test]
    fn test_generate_feature_doc_uses_reference_filename_for_extracted_examples() {
        let tempdir = tempdir().expect("tempdir");
        let doc = SspecDoc {
            file_path: PathBuf::from("test/specs/functions_spec.spl"),
            raw_content: String::new(),
            doc_blocks: vec![],
            feature_title: Some("Functions".to_string()),
            feature_ids: vec![],
            metadata: FeatureMetadata {
                source_doc: Some("functions.md".to_string()),
                doc_type: Some("Extracted Examples".to_string()),
                ..Default::default()
            },
        };

        generate_feature_doc(&doc, tempdir.path()).expect("generate doc");

        assert!(tempdir.path().join("functions.md").exists());
        assert!(!tempdir.path().join("functions_spec.md").exists());
    }

    #[test]
    fn test_preferred_feature_name_falls_back_from_placeholder_heading() {
        let doc = SspecDoc {
            file_path: PathBuf::from("test/specs/macro_spec.spl"),
            raw_content: String::new(),
            doc_blocks: vec![],
            feature_title: Some("- Test Specification".to_string()),
            feature_ids: vec![],
            metadata: FeatureMetadata {
                source_doc: Some("macro.md".to_string()),
                ..Default::default()
            },
        };

        assert_eq!(preferred_feature_name(&doc, "macro"), "Macro Specification");
    }

    #[test]
    fn test_extract_examples_parses_markers_docblocks_and_code() {
        let content = r#"
## Test: Functions (Line ~7)

"""
Functions in Simple are defined with the `fn` keyword.
"""
fn add(a: i64, b: i64) -> i64:
    return a + b

## Test: Closures (Line ~19)

"""
Closures capture variables.
"""
it "closures_1":
    expect(true).to_equal(true)
"#;

        let examples = extract_examples(content);
        assert_eq!(examples.len(), 2);
        assert_eq!(examples[0].title, "Functions");
        assert_eq!(examples[0].source_hint.as_deref(), Some("Line ~7"));
        assert_eq!(examples[0].kind, "Function example");
        assert_eq!(examples[0].scenario_name.as_deref(), Some("add"));
        assert!(examples[0].code.contains("fn add"));
        assert_eq!(examples[1].kind, "Scenario");
        assert_eq!(examples[1].scenario_name.as_deref(), Some("closures_1"));
    }

    #[test]
    fn test_generate_feature_doc_renders_example_details_for_extracted_specs() {
        let tempdir = tempdir().expect("tempdir");
        let doc = SspecDoc {
            file_path: PathBuf::from("test/specs/functions_spec.spl"),
            raw_content: r#"
## Test: Functions (Line ~7)

"""
Functions in Simple are defined with the `fn` keyword.
"""
fn add(a: i64, b: i64) -> i64:
    return a + b
"#
            .to_string(),
            doc_blocks: vec![super::super::types::DocBlock {
                content: r#"
# Simple Language Functions and Pattern Matching - Test Specification

**Status:** Reference
**Source:** functions.md
**Type:** Extracted Examples (Category B)

## Overview

This file contains executable test cases extracted from functions.md.
"#
                .trim()
                .to_string(),
                line_start: 0,
                line_end: 8,
            }],
            feature_title: Some("Simple Language Functions and Pattern Matching - Test Specification".to_string()),
            feature_ids: vec![],
            metadata: FeatureMetadata {
                status: Some("Reference".to_string()),
                source_doc: Some("functions.md".to_string()),
                doc_type: Some("Extracted Examples (Category B)".to_string()),
                ..Default::default()
            },
        };

        generate_feature_doc(&doc, tempdir.path()).expect("generate doc");

        let output = fs::read_to_string(tempdir.path().join("functions.md")).expect("read doc");
        assert!(output.contains("## Example Details"));
        assert!(output.contains("### 1. Functions"));
        assert!(output.contains("Kind: Function example"));
        assert!(output.contains("Reference: Line ~7"));
        assert!(output.contains("Scenario: `add`"));
        assert!(output.contains("```simple"));
        assert!(output.contains("fn add(a: i64, b: i64) -> i64:"));
    }
}
