//! Specification Coverage Tracking (#915)
//!
//! Measures how much of the language specification is covered by tests and implementations.

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug, Serialize, Deserialize)]
pub struct SpecCoverageFile {
    pub version: String,
    pub last_updated: String,
    pub categories: Vec<Category>,
    pub summary: Summary,
    pub category_coverage: HashMap<String, f64>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Category {
    pub id: String,
    pub name: String,
    pub features: Vec<Feature>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Feature {
    pub id: String,
    pub name: String,
    pub spec: String,
    pub status: Status,
    pub tests: Vec<String>,
    pub coverage: f64,
    #[serde(default)]
    pub missing: Vec<String>,
    #[serde(default)]
    pub notes: Option<String>,
}

#[derive(Debug, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "lowercase")]
pub enum Status {
    Implemented,
    Partial,
    Planned,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Summary {
    pub total_features: usize,
    pub implemented: usize,
    pub partial: usize,
    pub planned: usize,
    pub overall_coverage: f64,
}

pub struct SpecCoverageReport {
    data: SpecCoverageFile,
}

impl SpecCoverageReport {
    /// Load spec coverage data from YAML file
    pub fn load(path: &Path) -> Result<Self, String> {
        let content = fs::read_to_string(path).map_err(|e| format!("Failed to read spec file: {}", e))?;

        let data: SpecCoverageFile =
            serde_yaml::from_str(&content).map_err(|e| format!("Failed to parse YAML: {}", e))?;

        Ok(Self { data })
    }

    /// Display overall coverage statistics
    pub fn display_summary(&self) {
        println!("Simple Language Specification Coverage");
        println!();
        println!("Total features: {}", self.data.summary.total_features);
        println!(
            "Implemented: {} ({:.1}%)",
            self.data.summary.implemented,
            (self.data.summary.implemented as f64 / self.data.summary.total_features as f64) * 100.0
        );
        println!(
            "Partial: {} ({:.1}%)",
            self.data.summary.partial,
            (self.data.summary.partial as f64 / self.data.summary.total_features as f64) * 100.0
        );
        println!(
            "Planned: {} ({:.1}%)",
            self.data.summary.planned,
            (self.data.summary.planned as f64 / self.data.summary.total_features as f64) * 100.0
        );
        println!();
        println!("Overall Coverage: {:.1}%", self.data.summary.overall_coverage);
    }

    /// Display coverage by category
    pub fn display_by_category(&self) {
        println!("Coverage by Category:");
        println!();

        for (category_id, coverage) in &self.data.category_coverage {
            // Find the category name
            let category_name = self
                .data
                .categories
                .iter()
                .find(|c| c.id == *category_id)
                .map(|c| c.name.as_str())
                .unwrap_or(category_id);

            println!("  {}: {:.1}%", category_name, coverage);
        }
    }

    /// Display missing/incomplete features
    pub fn display_missing(&self) {
        println!("Missing/Incomplete Features:");
        println!();

        for category in &self.data.categories {
            for feature in &category.features {
                if feature.status == Status::Partial || feature.status == Status::Planned {
                    println!("  - {} (spec: {})", feature.name, feature.spec);

                    if !feature.missing.is_empty() {
                        for missing in &feature.missing {
                            println!("    • {}", missing);
                        }
                    }

                    if feature.status == Status::Partial {
                        println!("    Status: Partial ({:.1}% coverage)", feature.coverage);
                    } else {
                        println!("    Status: Planned");
                    }
                    println!();
                }
            }
        }
    }

    /// Generate HTML report
    pub fn generate_html(&self) -> String {
        let mut html = String::new();

        html.push_str("<!DOCTYPE html>\n<html>\n<head>\n");
        html.push_str("  <meta charset=\"UTF-8\">\n");
        html.push_str("  <title>Simple Language Spec Coverage Report</title>\n");
        html.push_str("  <style>\n");
        html.push_str("    body { font-family: system-ui, -apple-system, sans-serif; max-width: 1200px; margin: 0 auto; padding: 20px; }\n");
        html.push_str("    h1 { color: #333; }\n");
        html.push_str("    .summary { background: #f5f5f5; padding: 20px; border-radius: 8px; margin: 20px 0; }\n");
        html.push_str("    .metric { margin: 10px 0; }\n");
        html.push_str("    .metric .label { font-weight: bold; }\n");
        html.push_str("    .metric .value { font-size: 24px; color: #2196F3; }\n");
        html.push_str("    .progress { height: 20px; background: #e0e0e0; border-radius: 10px; margin-top: 5px; }\n");
        html.push_str(
            "    .progress-bar { height: 100%; background: #2196F3; border-radius: 10px; transition: width 0.3s; }\n",
        );
        html.push_str("    table { width: 100%; border-collapse: collapse; margin: 20px 0; }\n");
        html.push_str("    th { background: #333; color: white; padding: 12px; text-align: left; }\n");
        html.push_str("    td { padding: 10px; border-bottom: 1px solid #ddd; }\n");
        html.push_str("    .implemented { background: #e8f5e9; }\n");
        html.push_str("    .partial { background: #fff3e0; }\n");
        html.push_str("    .planned { background: #ffebee; }\n");
        html.push_str("    .category-section { margin: 30px 0; }\n");
        html.push_str("    .category-header { background: #f5f5f5; padding: 15px; margin: 20px 0; border-left: 4px solid #2196F3; }\n");
        html.push_str("  </style>\n");
        html.push_str("</head>\n<body>\n");

        html.push_str("  <h1>Simple Language Specification Coverage</h1>\n");

        // Summary section
        html.push_str("  <div class=\"summary\">\n");
        html.push_str(&format!("    <div class=\"metric\"><span class=\"label\">Overall Coverage:</span> <span class=\"value\">{:.1}%</span></div>\n", 
            self.data.summary.overall_coverage));
        html.push_str("    <div class=\"progress\">\n");
        html.push_str(&format!(
            "      <div class=\"progress-bar\" style=\"width: {:.1}%\"></div>\n",
            self.data.summary.overall_coverage
        ));
        html.push_str("    </div>\n");
        html.push_str(&format!(
            "    <p>Total Features: {} | Implemented: {} | Partial: {} | Planned: {}</p>\n",
            self.data.summary.total_features,
            self.data.summary.implemented,
            self.data.summary.partial,
            self.data.summary.planned
        ));
        html.push_str("  </div>\n");

        // Features by category
        for category in &self.data.categories {
            html.push_str("  <div class=\"category-section\">\n");
            html.push_str(&format!(
                "    <div class=\"category-header\"><h2>{}</h2></div>\n",
                category.name
            ));
            html.push_str("    <table>\n");
            html.push_str("      <tr><th>Feature</th><th>Status</th><th>Tests</th><th>Coverage</th></tr>\n");

            for feature in &category.features {
                let row_class = match feature.status {
                    Status::Implemented => "implemented",
                    Status::Partial => "partial",
                    Status::Planned => "planned",
                };

                let status_text = match feature.status {
                    Status::Implemented => "✓ Implemented",
                    Status::Partial => "⚠ Partial",
                    Status::Planned => "○ Planned",
                };

                html.push_str(&format!("      <tr class=\"{}\">\n", row_class));
                html.push_str(&format!("        <td>{}</td>\n", feature.name));
                html.push_str(&format!("        <td>{}</td>\n", status_text));
                html.push_str(&format!("        <td>{} test file(s)</td>\n", feature.tests.len()));
                html.push_str(&format!("        <td>{:.1}%</td>\n", feature.coverage));
                html.push_str("      </tr>\n");
            }

            html.push_str("    </table>\n");
            html.push_str("  </div>\n");
        }

        html.push_str(&format!("  <p><em>Generated: {}</em></p>\n", self.data.last_updated));
        html.push_str("</body>\n</html>");

        html
    }
}

/// Find the spec coverage file in the project root
pub fn find_spec_file() -> Result<PathBuf, String> {
    // Try specs/language.yaml in current directory and parents
    let mut current = std::env::current_dir().map_err(|e| format!("Failed to get current directory: {}", e))?;

    loop {
        let spec_path = current.join("specs").join("language.yaml");
        if spec_path.exists() {
            return Ok(spec_path);
        }

        if !current.pop() {
            break;
        }
    }

    Err("Could not find specs/language.yaml in current directory or parents".to_string())
}
