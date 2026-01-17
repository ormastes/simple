//! SSpec documentation generator
//!
//! Extracts markdown documentation from sspec test files ("""...""" blocks)
//! and generates comprehensive BDD-style documentation in doc/spec/
//!
//! ## Features
//!
//! - **Metadata Extraction:** Parses Feature ID, Category, Status, Difficulty
//! - **Categorized INDEX:** Groups features by category (Infrastructure, Language, etc.)
//! - **Validation:** Warns about missing documentation and incomplete specs
//! - **Statistics:** Tracks documentation coverage and quality metrics

mod generator;
mod index;
mod metadata;
mod parser;
mod types;
mod validation;

pub use types::{DocBlock, DocStats, FeatureMetadata, SspecDoc, ValidationResult};

use std::fs;
use std::path::{Path, PathBuf};

/// Generate SSpec documentation from spec files
///
/// Returns statistics about the generation process
pub fn generate_sspec_docs(sspec_files: &[PathBuf], output_dir: &Path) -> Result<DocStats, Box<dyn std::error::Error>> {
    fs::create_dir_all(output_dir)?;

    let mut stats = DocStats::default();
    let mut parsed_files = Vec::new();
    let mut validation_results = Vec::new();

    println!("\nGenerating BDD documentation...");
    println!("  Input files: {}", sspec_files.len());
    println!("  Output dir: {}\n", output_dir.display());

    println!("Processing specs:");

    // Parse all sspec files
    for file_path in sspec_files {
        match parser::parse_sspec_file(file_path) {
            Ok(mut parsed) => {
                // Extract metadata
                metadata::extract_metadata(&mut parsed);

                // Validate
                let validation = validation::validate_spec(&parsed);

                // Update stats
                stats.add_spec(validation.has_docs, validation.doc_lines, validation.warnings.len());

                // Print progress
                print_spec_status(&parsed, &validation);

                // Generate individual doc
                if let Err(e) = generator::generate_feature_doc(&parsed, output_dir) {
                    eprintln!("  ⚠️  Failed to generate doc for {}: {}", file_path.display(), e);
                }

                parsed_files.push((parsed, validation.clone()));
                validation_results.push(validation);
            }
            Err(e) => {
                eprintln!("  ✗ Failed to parse {}: {}", file_path.display(), e);
            }
        }
    }

    // Generate index page
    index::generate_index_page(&parsed_files, output_dir, &stats)?;

    // Print summary
    print_summary(&stats, &validation_results);

    Ok(stats)
}

/// Print status for a single spec
fn print_spec_status(sspec_doc: &SspecDoc, validation: &ValidationResult) {
    let filename = sspec_doc
        .file_path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("unknown");

    if validation.has_docs {
        if validation.warnings.is_empty() {
            println!("  ✅ {} ({} lines)", filename, validation.doc_lines);
        } else {
            println!(
                "  ⚠️  {} ({} lines, {} warnings)",
                filename,
                validation.doc_lines,
                validation.warnings.len()
            );
            for warning in &validation.warnings {
                println!("      → {}", warning);
            }
        }
    } else {
        println!("  ❌ {} - No documentation blocks found", filename);
    }
}

/// Print generation summary
fn print_summary(stats: &DocStats, validations: &[ValidationResult]) {
    println!("\n{}", "=".repeat(60));
    println!("Summary:");
    println!(
        "  Complete documentation: {}/{} ({:.0}%)",
        stats.specs_with_docs,
        stats.total_specs,
        stats.coverage_percent()
    );
    println!(
        "  Stubs: {}/{} ({:.0}%)",
        stats.specs_without_docs,
        stats.total_specs,
        (stats.specs_without_docs as f32 / stats.total_specs as f32) * 100.0
    );
    println!("  Total documentation: {} lines", stats.total_doc_lines);

    if stats.total_warnings > 0 {
        println!("  Warnings: {}", stats.total_warnings);

        // Show warning breakdown
        let mut warning_types: std::collections::HashMap<String, usize> = std::collections::HashMap::new();
        for validation in validations {
            for warning in &validation.warnings {
                let warning_type = if warning.contains("No documentation") {
                    "No documentation"
                } else if warning.contains("lines of documentation") {
                    "Short documentation"
                } else if warning.contains("Missing") {
                    "Missing sections"
                } else {
                    "Other"
                };
                *warning_types.entry(warning_type.to_string()).or_insert(0) += 1;
            }
        }

        println!("\n  Warning breakdown:");
        for (warning_type, count) in warning_types {
            println!("    - {}: {}", warning_type, count);
        }
    }

    println!("{}", "=".repeat(60));
    println!("\n✓ Documentation generated successfully!");
}
