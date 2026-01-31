//! note.sdn section loader for SMF files.
//!
//! This module reads and parses the note.sdn section from SMF files,
//! enabling lazy instantiation and circular dependency detection.
//!
//! Phase 2: note.sdn Reading (Loader)

use std::collections::HashMap;
use std::io::{Read, Seek, SeekFrom};

use super::section::SmfSection;

/// The terminator that marks the end of note.sdn data.
pub const NOTE_SDN_TERMINATOR: &str = "\n# END_NOTE\n";

/// Loaded note.sdn metadata from an SMF file.
#[derive(Debug, Clone, Default)]
pub struct LoadedNoteSdn {
    /// Template instantiations that were compiled
    pub instantiations: Vec<LoadedInstantiation>,
    /// Possible instantiations that can be lazily generated
    pub possible: Vec<LoadedPossible>,
    /// Type inference events
    pub type_inferences: Vec<LoadedTypeInference>,
    /// Dependency graph edges
    pub dependencies: Vec<LoadedDependency>,
    /// Circular dependency warnings
    pub circular_warnings: Vec<LoadedCircularWarning>,
    /// Circular dependency errors
    pub circular_errors: Vec<LoadedCircularError>,
}

impl LoadedNoteSdn {
    /// Create empty loaded metadata
    pub fn new() -> Self {
        Self::default()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.instantiations.is_empty()
            && self.possible.is_empty()
            && self.type_inferences.is_empty()
            && self.dependencies.is_empty()
            && self.circular_warnings.is_empty()
            && self.circular_errors.is_empty()
    }

    /// Find an instantiation by mangled name
    pub fn find_instantiation(&self, mangled_name: &str) -> Option<&LoadedInstantiation> {
        self.instantiations.iter().find(|i| i.mangled_name == mangled_name)
    }

    /// Find a possible instantiation by mangled name
    pub fn find_possible(&self, mangled_name: &str) -> Option<&LoadedPossible> {
        self.possible.iter().find(|p| p.mangled_name == mangled_name)
    }

    /// Get all dependencies from a given instantiation
    pub fn get_dependencies_from(&self, from_inst: &str) -> Vec<&LoadedDependency> {
        self.dependencies.iter().filter(|d| d.from_inst == from_inst).collect()
    }

    /// Get all dependencies to a given instantiation
    pub fn get_dependencies_to(&self, to_inst: &str) -> Vec<&LoadedDependency> {
        self.dependencies.iter().filter(|d| d.to_inst == to_inst).collect()
    }

    /// Check if there are any circular errors
    pub fn has_circular_errors(&self) -> bool {
        !self.circular_errors.is_empty()
    }

    /// Build a dependency graph as adjacency list
    pub fn build_dependency_graph(&self) -> HashMap<String, Vec<String>> {
        let mut graph: HashMap<String, Vec<String>> = HashMap::new();
        for dep in &self.dependencies {
            graph
                .entry(dep.from_inst.clone())
                .or_default()
                .push(dep.to_inst.clone());
        }
        graph
    }
}

/// A loaded instantiation entry.
#[derive(Debug, Clone)]
pub struct LoadedInstantiation {
    pub id: u32,
    pub template: String,
    pub type_args: String,
    pub mangled_name: String,
    pub from_file: String,
    pub from_loc: String,
    pub to_obj: String,
    pub status: String,
}

/// A loaded possible instantiation entry.
#[derive(Debug, Clone)]
pub struct LoadedPossible {
    pub id: u32,
    pub template: String,
    pub type_args: String,
    pub mangled_name: String,
    pub required_by: String,
    pub can_defer: bool,
}

/// A loaded type inference entry.
#[derive(Debug, Clone)]
pub struct LoadedTypeInference {
    pub id: u32,
    pub inferred_type: String,
    pub expr: String,
    pub context: String,
    pub from_file: String,
    pub from_loc: String,
}

/// A loaded dependency edge.
#[derive(Debug, Clone)]
pub struct LoadedDependency {
    pub from_inst: String,
    pub to_inst: String,
    pub dep_kind: String,
}

/// A loaded circular warning.
#[derive(Debug, Clone)]
pub struct LoadedCircularWarning {
    pub id: u32,
    pub cycle_path: String,
    pub severity: String,
}

/// A loaded circular error.
#[derive(Debug, Clone)]
pub struct LoadedCircularError {
    pub id: u32,
    pub cycle_path: String,
    pub error_code: String,
}

/// Load note.sdn section from an SMF file reader.
///
/// Uses the zero-size trick: scans from section offset until terminator.
pub fn load_note_sdn<R: Read + Seek>(reader: &mut R, section: &SmfSection) -> Result<LoadedNoteSdn, String> {
    // Seek to section offset
    reader
        .seek(SeekFrom::Start(section.offset))
        .map_err(|e| format!("Failed to seek to note.sdn section: {}", e))?;

    // Read until we find the terminator (zero-size trick)
    let content = read_until_terminator(reader, NOTE_SDN_TERMINATOR)?;

    // Parse the SDN content
    parse_note_sdn(&content)
}

/// Read from reader until terminator is found.
fn read_until_terminator<R: Read>(reader: &mut R, terminator: &str) -> Result<String, String> {
    let mut content = String::new();
    let mut buffer = [0u8; 4096];
    let terminator_bytes = terminator.as_bytes();

    loop {
        let bytes_read = reader
            .read(&mut buffer)
            .map_err(|e| format!("Failed to read note.sdn: {}", e))?;

        if bytes_read == 0 {
            return Err("Reached EOF without finding terminator".to_string());
        }

        let chunk = String::from_utf8_lossy(&buffer[..bytes_read]);
        content.push_str(&chunk);

        // Check if we have the terminator
        if content.contains(terminator) {
            // Trim content up to and including terminator
            if let Some(pos) = content.find(terminator) {
                content.truncate(pos + terminator.len());
            }
            break;
        }

        // Safety limit: 1MB max
        if content.len() > 1_000_000 {
            return Err("note.sdn section too large (> 1MB)".to_string());
        }
    }

    Ok(content)
}

/// Parse SDN content into LoadedNoteSdn.
pub fn parse_note_sdn(content: &str) -> Result<LoadedNoteSdn, String> {
    let mut result = LoadedNoteSdn::new();
    let mut current_table: Option<&str> = None;
    // TODO(sdn): Use parsed columns for table validation
    let mut _columns: Vec<String> = Vec::new();

    for line in content.lines() {
        let line = line.trim();

        // Skip empty lines and comments (except table headers)
        if line.is_empty() || (line.starts_with('#') && !line.contains('|')) {
            continue;
        }

        // Check for table header
        if line.contains('|') && !line.starts_with('\"') && !line.chars().next().unwrap_or(' ').is_ascii_digit() {
            // Parse table header: "tablename |col1, col2, ...|"
            let parts: Vec<&str> = line.splitn(2, '|').collect();
            if parts.len() >= 2 {
                let table_name = parts[0].trim();
                let cols_str = parts[1].trim_end_matches('|');
                _columns = cols_str.split(',').map(|s| s.trim().to_string()).collect();
                current_table = Some(match table_name {
                    "instantiations" => "instantiations",
                    "possible" => "possible",
                    "type_inferences" => "type_inferences",
                    "dependencies" => "dependencies",
                    "circular_warnings" => "circular_warnings",
                    "circular_errors" => "circular_errors",
                    _ => continue,
                });
            }
            continue;
        }

        // Parse data row
        if let Some(table) = current_table {
            let values = parse_sdn_row(line)?;

            match table {
                "instantiations" => {
                    if values.len() >= 8 {
                        result.instantiations.push(LoadedInstantiation {
                            id: values[0].parse().unwrap_or(0),
                            template: unescape_sdn(&values[1]),
                            type_args: unescape_sdn(&values[2]),
                            mangled_name: unescape_sdn(&values[3]),
                            from_file: unescape_sdn(&values[4]),
                            from_loc: unescape_sdn(&values[5]),
                            to_obj: unescape_sdn(&values[6]),
                            status: unescape_sdn(&values[7]),
                        });
                    }
                }
                "possible" => {
                    if values.len() >= 6 {
                        result.possible.push(LoadedPossible {
                            id: values[0].parse().unwrap_or(0),
                            template: unescape_sdn(&values[1]),
                            type_args: unescape_sdn(&values[2]),
                            mangled_name: unescape_sdn(&values[3]),
                            required_by: unescape_sdn(&values[4]),
                            can_defer: values[5].trim() == "true",
                        });
                    }
                }
                "type_inferences" => {
                    if values.len() >= 6 {
                        result.type_inferences.push(LoadedTypeInference {
                            id: values[0].parse().unwrap_or(0),
                            inferred_type: unescape_sdn(&values[1]),
                            expr: unescape_sdn(&values[2]),
                            context: unescape_sdn(&values[3]),
                            from_file: unescape_sdn(&values[4]),
                            from_loc: unescape_sdn(&values[5]),
                        });
                    }
                }
                "dependencies" => {
                    if values.len() >= 3 {
                        result.dependencies.push(LoadedDependency {
                            from_inst: unescape_sdn(&values[0]),
                            to_inst: unescape_sdn(&values[1]),
                            dep_kind: unescape_sdn(&values[2]),
                        });
                    }
                }
                "circular_warnings" => {
                    if values.len() >= 3 {
                        result.circular_warnings.push(LoadedCircularWarning {
                            id: values[0].parse().unwrap_or(0),
                            cycle_path: unescape_sdn(&values[1]),
                            severity: unescape_sdn(&values[2]),
                        });
                    }
                }
                "circular_errors" => {
                    if values.len() >= 3 {
                        result.circular_errors.push(LoadedCircularError {
                            id: values[0].parse().unwrap_or(0),
                            cycle_path: unescape_sdn(&values[1]),
                            error_code: unescape_sdn(&values[2]),
                        });
                    }
                }
                _ => {}
            }
        }
    }

    Ok(result)
}

/// Parse an SDN data row into values.
fn parse_sdn_row(line: &str) -> Result<Vec<String>, String> {
    let mut values = Vec::new();
    let mut current = String::new();
    let mut in_quotes = false;
    let mut escape_next = false;

    for ch in line.chars() {
        if escape_next {
            current.push(ch);
            escape_next = false;
            continue;
        }

        match ch {
            '\\' => escape_next = true,
            '"' => {
                in_quotes = !in_quotes;
            }
            ',' if !in_quotes => {
                values.push(current.trim().to_string());
                current = String::new();
            }
            _ => current.push(ch),
        }
    }

    // Don't forget the last value
    if !current.is_empty() {
        values.push(current.trim().to_string());
    }

    Ok(values)
}

/// Unescape SDN string values.
fn unescape_sdn(s: &str) -> String {
    // Remove surrounding quotes if present
    let s = s.trim();
    let s = if s.starts_with('"') && s.ends_with('"') {
        &s[1..s.len() - 1]
    } else {
        s
    };

    s.replace("\\\"", "\"")
        .replace("\\\\", "\\")
        .replace("\\n", "\n")
        .replace("\\r", "\r")
        .replace("\\t", "\t")
}

/// Find note.sdn section in section list by name.
pub fn find_note_sdn_section(sections: &[SmfSection]) -> Option<&SmfSection> {
    sections.iter().find(|s| s.name_str() == "note.sdn")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_empty_note_sdn() {
        let content = r#"
# Instantiation To/From Metadata
# Format version: 1.0

instantiations |id, template, type_args, mangled_name, from_file, from_loc, to_obj, status|

possible |id, template, type_args, mangled_name, required_by, can_defer|

type_inferences |id, inferred_type, expr, context, from_file, from_loc|

dependencies |from_inst, to_inst, dep_kind|

circular_warnings |id, cycle_path, severity|

circular_errors |id, cycle_path, error_code|

# END_NOTE
"#;
        let result = parse_note_sdn(content).unwrap();
        assert!(result.is_empty());
    }

    #[test]
    fn test_parse_instantiation() {
        let content = r#"
instantiations |id, template, type_args, mangled_name, from_file, from_loc, to_obj, status|
    0, "List", "Int", "List$Int", "app.spl", "app.spl:10:5", "app.o", "compiled"

# END_NOTE
"#;
        let result = parse_note_sdn(content).unwrap();
        assert_eq!(result.instantiations.len(), 1);
        assert_eq!(result.instantiations[0].template, "List");
        assert_eq!(result.instantiations[0].type_args, "Int");
        assert_eq!(result.instantiations[0].mangled_name, "List$Int");
    }

    #[test]
    fn test_parse_dependency() {
        let content = r#"
dependencies |from_inst, to_inst, dep_kind|
    "List$Int", "Int", "type_param"

# END_NOTE
"#;
        let result = parse_note_sdn(content).unwrap();
        assert_eq!(result.dependencies.len(), 1);
        assert_eq!(result.dependencies[0].from_inst, "List$Int");
        assert_eq!(result.dependencies[0].to_inst, "Int");
        assert_eq!(result.dependencies[0].dep_kind, "type_param");
    }

    #[test]
    fn test_unescape_sdn() {
        assert_eq!(unescape_sdn("\"hello\""), "hello");
        assert_eq!(unescape_sdn("\"test\\\"quote\""), "test\"quote");
        assert_eq!(unescape_sdn("\"back\\\\slash\""), "back\\slash");
        assert_eq!(unescape_sdn("\"new\\nline\""), "new\nline");
    }

    #[test]
    fn test_build_dependency_graph() {
        let content = r#"
dependencies |from_inst, to_inst, dep_kind|
    "Container$List$Int", "List$Int", "field_type"
    "List$Int", "Int", "type_param"

# END_NOTE
"#;
        let result = parse_note_sdn(content).unwrap();
        let graph = result.build_dependency_graph();

        assert!(graph.contains_key("Container$List$Int"));
        assert!(graph.contains_key("List$Int"));
        assert_eq!(graph["Container$List$Int"], vec!["List$Int"]);
        assert_eq!(graph["List$Int"], vec!["Int"]);
    }
}
