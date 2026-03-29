//! Generate individual feature documentation files

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

use chrono::Local;

use super::types::SspecDoc;

/// Generate documentation for a single feature
pub fn generate_feature_doc(sspec_doc: &SspecDoc, output_dir: &Path) -> Result<(), Box<dyn std::error::Error>> {
    let file_name = sspec_doc
        .file_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("unknown");

    let feature_name = sspec_doc
        .feature_title
        .clone()
        .unwrap_or_else(|| humanize_filename(file_name));

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
        rows.push((
            "Dependencies".to_string(),
            sspec_doc.metadata.dependencies.join(", "),
        ));
    }
    rows.push(("Source".to_string(), format!("`{}`", sspec_doc.file_path.display())));
    rows.push((
        "Updated".to_string(),
        Local::now().format("%Y-%m-%d").to_string(),
    ));
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
                    "target/test-artifacts/app/web_dashboard/tmux_rest_api/result.json".to_string(),
                    "target/test-artifacts/app/web_dashboard/tmux_rest_api/notes.txt".to_string(),
                ],
                screenshots: vec!["doc/spec/image/app/web_dashboard/tmux_rest_api/shot.png".to_string()],
                tui_captures: vec!["target/test-artifacts/app/web_dashboard/tmux_rest_api/terminal.ansi".to_string()],
                logs: vec!["target/test-artifacts/app/web_dashboard/tmux_rest_api/run.log".to_string()],
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
}
