//! Generate individual feature documentation files

use std::fs;
use std::io::Write;
use std::path::Path;

use super::types::SspecDoc;

/// Generate documentation for a single feature
pub fn generate_feature_doc(sspec_doc: &SspecDoc, output_dir: &Path) -> Result<(), Box<dyn std::error::Error>> {
    let file_name = sspec_doc
        .file_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("unknown");

    let feature_name = sspec_doc.feature_title.as_deref().unwrap_or(file_name);

    let mut md = String::new();

    // Add header
    md.push_str(&format!("# {}\n\n", feature_name));
    md.push_str(&format!("*Source: `{}`*\n\n", sspec_doc.file_path.display()));

    // Add feature IDs if present
    if !sspec_doc.feature_ids.is_empty() {
        md.push_str("## Feature IDs\n\n");
        for id in &sspec_doc.feature_ids {
            let anchor = id.replace('.', "-");
            md.push_str(&format!("- <a id=\"feature-{}\"></a>{}\n", anchor, id));
        }
        md.push_str("\n");
    }

    md.push_str("---\n\n");

    // Add all documentation blocks
    for (idx, doc_block) in sspec_doc.doc_blocks.iter().enumerate() {
        if idx > 0 {
            md.push_str("\n");
        }
        md.push_str(&doc_block.content);
        md.push_str("\n");
    }

    // Write to file
    let output_path = output_dir.join(format!("{}.md", file_name));
    let mut file = fs::File::create(output_path)?;
    file.write_all(md.as_bytes())?;

    Ok(())
}
