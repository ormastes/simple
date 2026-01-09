//! Diagram generation from profiler sequence events
//!
//! Generates Mermaid diagrams from recorded call sequences:
//! - Sequence diagrams (sequenceDiagram)
//! - Class diagrams (classDiagram)
//! - Architecture diagrams (flowchart TD)

use std::collections::{HashMap, HashSet};

use super::config::{CallType, SequenceEvent};
use super::profiler::RuntimeProfiler;

/// Diagram output format
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum DiagramFormat {
    #[default]
    Mermaid,
    PlantUml,
    Text,
}

/// Diagram generation options
#[derive(Debug, Clone, Default)]
pub struct DiagramOptions {
    /// Include timing information
    pub include_timing: bool,
    /// Include argument values
    pub include_args: bool,
    /// Include return values
    pub include_returns: bool,
    /// Maximum events to include (0 = unlimited)
    pub max_events: usize,
    /// Include filter patterns
    pub include_patterns: Vec<String>,
    /// Exclude filter patterns
    pub exclude_patterns: Vec<String>,
}

impl DiagramOptions {
    pub fn new() -> Self {
        Self {
            include_timing: true,
            include_args: true,
            include_returns: true,
            max_events: 0,
            include_patterns: Vec::new(),
            exclude_patterns: Vec::new(),
        }
    }

    pub fn with_timing(mut self, include: bool) -> Self {
        self.include_timing = include;
        self
    }

    pub fn with_args(mut self, include: bool) -> Self {
        self.include_args = include;
        self
    }

    pub fn with_returns(mut self, include: bool) -> Self {
        self.include_returns = include;
        self
    }

    pub fn with_max_events(mut self, max: usize) -> Self {
        self.max_events = max;
        self
    }

    pub fn with_include(mut self, pattern: &str) -> Self {
        self.include_patterns.push(pattern.to_string());
        self
    }

    pub fn with_exclude(mut self, pattern: &str) -> Self {
        self.exclude_patterns.push(pattern.to_string());
        self
    }
}

/// Generate a Mermaid sequence diagram from profiler events
pub fn generate_sequence_diagram(profiler: &RuntimeProfiler, options: &DiagramOptions) -> String {
    let events = profiler.get_sequence_events();
    generate_sequence_from_events(&events, options)
}

/// Generate a Mermaid sequence diagram from events
pub fn generate_sequence_from_events(events: &[SequenceEvent], options: &DiagramOptions) -> String {
    let filtered = filter_events(events, options);
    let limited = if options.max_events > 0 && filtered.len() > options.max_events {
        &filtered[..options.max_events]
    } else {
        &filtered[..]
    };

    let mut output = String::new();
    output.push_str("```mermaid\n");
    output.push_str("sequenceDiagram\n");
    output.push_str("    autonumber\n");

    // Collect participants
    let mut participants: HashMap<String, String> = HashMap::new();
    for event in limited {
        let caller = event.caller_participant().to_string();
        let callee = event.callee_participant().to_string();

        if !participants.contains_key(&caller) {
            let alias = create_alias(&caller);
            participants.insert(caller.clone(), alias);
        }
        if !participants.contains_key(&callee) {
            let alias = create_alias(&callee);
            participants.insert(callee.clone(), alias);
        }
    }

    // Emit participants
    for (name, alias) in &participants {
        output.push_str(&format!("    participant {} as {}\n", alias, name));
    }
    output.push('\n');

    // Emit events
    for event in limited {
        let caller_alias = participants.get(event.caller_participant()).unwrap();
        let callee_alias = participants.get(event.callee_participant()).unwrap();

        if event.is_return {
            // Return arrow
            output.push_str(&format!("    deactivate {}\n", callee_alias));
            if options.include_returns {
                if let Some(ref ret_val) = event.return_value {
                    output.push_str(&format!(
                        "    {}-->>{}:{}\n",
                        callee_alias, caller_alias, ret_val
                    ));
                }
            }
        } else {
            // Call arrow
            if options.include_timing {
                output.push_str(&format!(
                    "    Note over {}: {}us\n",
                    caller_alias,
                    event.timestamp_ns / 1000
                ));
            }

            let label = if options.include_args && !event.arguments.is_empty() {
                format!("{}({})", event.callee, event.arguments.join(", "))
            } else {
                event.callee.clone()
            };

            output.push_str(&format!(
                "    {}->>{}:{}\n",
                caller_alias, callee_alias, label
            ));
            output.push_str(&format!("    activate {}\n", callee_alias));
        }
    }

    output.push_str("```\n");
    output
}

/// Generate a Mermaid class diagram from profiler events
pub fn generate_class_diagram(profiler: &RuntimeProfiler, options: &DiagramOptions) -> String {
    let events = profiler.get_sequence_events();
    generate_class_from_events(&events, options)
}

/// Generate a Mermaid class diagram from events
pub fn generate_class_from_events(events: &[SequenceEvent], options: &DiagramOptions) -> String {
    let filtered = filter_events(events, options);

    // Extract classes and methods
    let mut classes: HashMap<String, HashSet<String>> = HashMap::new();
    let mut relations: HashSet<(String, String)> = HashSet::new();

    for event in &filtered {
        if event.is_return {
            continue;
        }

        // Track callee class
        if let Some(ref cls) = event.callee_class {
            classes
                .entry(cls.clone())
                .or_default()
                .insert(event.callee.clone());
        }

        // Track relationships
        if let (Some(ref from_cls), Some(ref to_cls)) = (&event.caller_class, &event.callee_class) {
            if from_cls != to_cls {
                relations.insert((from_cls.clone(), to_cls.clone()));
            }
        }
    }

    let mut output = String::new();
    output.push_str("```mermaid\n");
    output.push_str("classDiagram\n");

    // Emit classes
    for (class_name, methods) in &classes {
        output.push_str(&format!("    class {} {{\n", class_name));
        for method in methods {
            output.push_str(&format!("        +{}()\n", method));
        }
        output.push_str("    }\n");
    }

    output.push('\n');

    // Emit relations
    for (from, to) in &relations {
        output.push_str(&format!("    {} --> {} : uses\n", from, to));
    }

    output.push_str("```\n");
    output
}

/// Generate a Mermaid architecture diagram from profiler events
pub fn generate_arch_diagram(profiler: &RuntimeProfiler, options: &DiagramOptions) -> String {
    let events = profiler.get_sequence_events();
    let architectural = profiler.get_architectural_entities();
    generate_arch_from_events(&events, &architectural, options)
}

/// Generate a Mermaid architecture diagram from events
pub fn generate_arch_from_events(
    events: &[SequenceEvent],
    architectural: &HashSet<String>,
    options: &DiagramOptions,
) -> String {
    let filtered = filter_events(events, options);

    // Extract architectural entities and dependencies
    let mut entities: HashSet<String> = HashSet::new();
    let mut dependencies: HashSet<(String, String)> = HashSet::new();
    let mut packages: HashMap<String, Vec<String>> = HashMap::new();

    for event in &filtered {
        if event.is_return {
            continue;
        }

        let caller = event.caller_participant();
        let callee = event.callee_participant();

        // Check if architectural
        let caller_arch = is_architectural(caller, architectural);
        let callee_arch = is_architectural(callee, architectural);

        if caller_arch {
            entities.insert(caller.to_string());
            if let Some(pkg) = get_package(caller) {
                packages.entry(pkg).or_default().push(caller.to_string());
            }
        }
        if callee_arch {
            entities.insert(callee.to_string());
            if let Some(pkg) = get_package(callee) {
                packages.entry(pkg).or_default().push(callee.to_string());
            }
        }

        if caller_arch && callee_arch && caller != callee {
            dependencies.insert((caller.to_string(), callee.to_string()));
        }
    }

    let mut output = String::new();
    output.push_str("```mermaid\n");
    output.push_str("flowchart TD\n");

    // Emit subgraphs for packages
    let mut emitted: HashSet<String> = HashSet::new();
    for (pkg, members) in &packages {
        output.push_str(&format!("    subgraph {}[\"{}\"]\n", sanitize_id(pkg), pkg));
        for member in members {
            if !emitted.contains(member) {
                let short_name = member.split('.').last().unwrap_or(member);
                output.push_str(&format!(
                    "        {}[{}]\n",
                    sanitize_id(member),
                    short_name
                ));
                emitted.insert(member.clone());
            }
        }
        output.push_str("    end\n");
    }

    // Emit standalone entities
    for entity in &entities {
        if !emitted.contains(entity) {
            output.push_str(&format!("    {}[{}]\n", sanitize_id(entity), entity));
        }
    }

    output.push('\n');

    // Emit dependencies
    for (from, to) in &dependencies {
        output.push_str(&format!(
            "    {} --> {}\n",
            sanitize_id(from),
            sanitize_id(to)
        ));
    }

    output.push_str("```\n");
    output
}

// Helper functions

fn create_alias(name: &str) -> String {
    if name.len() <= 8 {
        return name.to_string();
    }

    // Try abbreviation from uppercase letters
    let abbrev: String = name.chars().filter(|c| c.is_uppercase()).collect();
    if abbrev.len() >= 2 {
        return abbrev;
    }

    // Fall back to first 6 chars
    name.chars().take(6).collect()
}

fn sanitize_id(name: &str) -> String {
    name.chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

fn is_architectural(name: &str, architectural: &HashSet<String>) -> bool {
    // Explicitly marked
    if architectural.contains(name) {
        return true;
    }

    // Packages are architectural by default
    if name.contains('.') || name.contains("::") {
        return true;
    }

    false
}

fn get_package(name: &str) -> Option<String> {
    if name.contains('.') {
        return Some(name.split('.').next()?.to_string());
    }
    if name.contains("::") {
        return Some(name.split("::").next()?.to_string());
    }
    None
}

fn filter_events(events: &[SequenceEvent], options: &DiagramOptions) -> Vec<SequenceEvent> {
    events
        .iter()
        .filter(|event| {
            let caller = event.caller_participant();
            let callee = event.callee_participant();

            // Check excludes first
            for pattern in &options.exclude_patterns {
                if matches_pattern(caller, pattern) || matches_pattern(callee, pattern) {
                    return false;
                }
            }

            // If no includes, include all
            if options.include_patterns.is_empty() {
                return true;
            }

            // Must match at least one include
            for pattern in &options.include_patterns {
                if matches_pattern(caller, pattern) || matches_pattern(callee, pattern) {
                    return true;
                }
            }

            false
        })
        .cloned()
        .collect()
}

fn matches_pattern(name: &str, pattern: &str) -> bool {
    // Simple glob matching
    if pattern == "*" {
        return true;
    }

    if pattern.starts_with('*') && pattern.ends_with('*') {
        let middle = &pattern[1..pattern.len() - 1];
        return name.contains(middle);
    }

    if pattern.starts_with('*') {
        let suffix = &pattern[1..];
        return name.ends_with(suffix);
    }

    if pattern.ends_with('*') {
        let prefix = &pattern[..pattern.len() - 1];
        return name.starts_with(prefix);
    }

    name == pattern
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_alias() {
        assert_eq!(create_alias("User"), "User");
        assert_eq!(create_alias("UserService"), "US");
        assert_eq!(create_alias("VeryLongClassName"), "VLCN");
    }

    #[test]
    fn test_sanitize_id() {
        assert_eq!(sanitize_id("app.services.User"), "app_services_User");
        assert_eq!(sanitize_id("crate::module::Type"), "crate__module__Type");
    }

    #[test]
    fn test_matches_pattern() {
        assert!(matches_pattern("UserService", "*Service"));
        assert!(matches_pattern("UserService", "User*"));
        assert!(matches_pattern("UserService", "*erSer*"));
        assert!(!matches_pattern("UserService", "*Helper"));
    }
}
