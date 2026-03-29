//! Generate individual feature documentation files

use std::fs;
use std::io::Write;
use std::path::Path;

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
    md.push_str(&format!("*Source: `{}`*\n", sspec_doc.file_path.display()));
    md.push_str(&format!(
        "*Last Updated: {}*\n\n",
        Local::now().format("%Y-%m-%d")
    ));

    let metadata_lines = build_metadata_lines(sspec_doc);
    if !metadata_lines.is_empty() {
        for line in metadata_lines {
            md.push_str(&line);
            md.push('\n');
        }
        md.push('\n');
    }

    md.push_str("---\n\n");

    if let Some(first_block) = sspec_doc.doc_blocks.first() {
        let first_content = strip_header_metadata(&first_block.content);
        if !first_content.is_empty() {
            md.push_str(&first_content);
            md.push_str("\n\n");
        }

        for doc_block in sspec_doc.doc_blocks.iter().skip(1) {
            md.push_str(doc_block.content.trim());
            md.push_str("\n\n");
        }
    } else {
        md.push_str("## Overview\n\n");
        md.push_str("Documentation was generated from executable SSpec scenarios.\n\n");
    }

    let scenarios = extract_scenarios(&sspec_doc.raw_content);
    if !scenarios.is_empty() {
        md.push_str("## Test Summary\n\n");
        md.push_str("| Metric | Count |\n");
        md.push_str("|--------|-------|\n");
        md.push_str(&format!("| Scenarios | {} |\n", scenarios.len()));
        md.push_str(&format!(
            "| Slow Scenarios | {} |\n",
            scenarios.iter().filter(|s| s.kind == ScenarioKind::Slow).count()
        ));
        md.push_str(&format!(
            "| Skipped Scenarios | {} |\n",
            scenarios.iter().filter(|s| s.kind == ScenarioKind::Skipped).count()
        ));
        md.push('\n');

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

fn build_metadata_lines(sspec_doc: &SspecDoc) -> Vec<String> {
    let mut lines = Vec::new();

    if let Some(id) = sspec_doc
        .metadata
        .id
        .clone()
        .or_else(|| (!sspec_doc.feature_ids.is_empty()).then(|| sspec_doc.feature_ids.join(", ")))
    {
        lines.push(format!("**Feature IDs:** {}", id));
    }
    if let Some(category) = &sspec_doc.metadata.category {
        lines.push(format!("**Category:** {}", category));
    }
    if let Some(difficulty) = &sspec_doc.metadata.difficulty {
        lines.push(format!("**Difficulty:** {}", difficulty));
    }
    if let Some(status) = &sspec_doc.metadata.status {
        lines.push(format!("**Status:** {}", status));
    }
    if let Some(requirements) = &sspec_doc.metadata.requirements {
        lines.push(format!("**Requirements:** {}", requirements));
    }
    if let Some(plan) = &sspec_doc.metadata.plan {
        lines.push(format!("**Plan:** {}", plan));
    }
    if let Some(design) = &sspec_doc.metadata.design {
        lines.push(format!("**Design:** {}", design));
    }
    if let Some(research) = &sspec_doc.metadata.research {
        lines.push(format!("**Research:** {}", research));
    }

    lines
}

fn strip_header_metadata(content: &str) -> String {
    let mut out = Vec::new();
    let mut skipping_leading_blanks = true;

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
            || trimmed.starts_with("**Research:**");

        if trimmed.starts_with("# ") || is_metadata {
            continue;
        }

        if skipping_leading_blanks && trimmed.is_empty() {
            continue;
        }

        skipping_leading_blanks = false;
        out.push(line);
    }

    out.join("\n").trim().to_string()
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
