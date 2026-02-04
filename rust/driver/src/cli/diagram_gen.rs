//! Diagram generation CLI
//!
//! Provides command-line interface for generating diagrams from:
//! - Test execution traces
//! - Profile data
//! - Source code analysis
//!
//! Output formats: Mermaid (default), PlantUML, Text

use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

use simple_compiler::runtime_profile::{
    generate_arch_from_events, generate_class_from_events, generate_sequence_from_events, CallType, DiagramOptions,
    ProfileConfig, ProfileMode, RuntimeProfiler, SequenceEvent,
};

/// Diagram type to generate
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagramType {
    Sequence,
    Class,
    Architecture,
    All,
}

/// Options for diagram generation CLI
#[derive(Debug, Clone)]
pub struct DiagramGenOptions {
    /// Diagram types to generate
    pub diagram_types: Vec<DiagramType>,
    /// Include filter patterns
    pub include_patterns: Vec<String>,
    /// Exclude filter patterns
    pub exclude_patterns: Vec<String>,
    /// Output directory
    pub output_dir: PathBuf,
    /// Include timing in diagrams
    pub include_timing: bool,
    /// Include arguments
    pub include_args: bool,
    /// Include return values
    pub include_returns: bool,
    /// Maximum events per diagram
    pub max_events: usize,
    /// Test name (for output file naming)
    pub test_name: String,
    /// Profile data file to load from
    pub from_file: Option<PathBuf>,
}

impl Default for DiagramGenOptions {
    fn default() -> Self {
        Self {
            diagram_types: vec![DiagramType::Sequence],
            include_patterns: Vec::new(),
            exclude_patterns: Vec::new(),
            output_dir: PathBuf::from("target/diagrams"),
            include_timing: true,
            include_args: true,
            include_returns: true,
            max_events: 0,
            test_name: "diagram".to_string(),
            from_file: None,
        }
    }
}

impl DiagramGenOptions {
    pub fn new(test_name: &str) -> Self {
        Self {
            test_name: test_name.to_string(),
            ..Default::default()
        }
    }

    pub fn with_type(mut self, diagram_type: DiagramType) -> Self {
        if !self.diagram_types.contains(&diagram_type) {
            self.diagram_types.push(diagram_type);
        }
        self
    }

    pub fn with_all_types(mut self) -> Self {
        self.diagram_types = vec![DiagramType::Sequence, DiagramType::Class, DiagramType::Architecture];
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

    pub fn with_output_dir(mut self, dir: &Path) -> Self {
        self.output_dir = dir.to_path_buf();
        self
    }

    pub fn to_diagram_options(&self) -> DiagramOptions {
        let mut opts = DiagramOptions::new()
            .with_timing(self.include_timing)
            .with_args(self.include_args)
            .with_returns(self.include_returns)
            .with_max_events(self.max_events);

        for pattern in &self.include_patterns {
            opts = opts.with_include(pattern);
        }
        for pattern in &self.exclude_patterns {
            opts = opts.with_exclude(pattern);
        }

        opts
    }
}

/// Result of diagram generation
#[derive(Debug)]
pub struct DiagramResult {
    pub sequence_path: Option<PathBuf>,
    pub class_path: Option<PathBuf>,
    pub arch_path: Option<PathBuf>,
    pub sequence_content: Option<String>,
    pub class_content: Option<String>,
    pub arch_content: Option<String>,
}

/// Generate diagrams from a profiler instance
pub fn generate_diagrams(profiler: &RuntimeProfiler, options: &DiagramGenOptions) -> Result<DiagramResult, String> {
    let events = profiler.get_sequence_events();
    let architectural = profiler.get_architectural_entities();
    generate_diagrams_from_events(&events, &architectural, options)
}

/// Generate diagrams from sequence events
pub fn generate_diagrams_from_events(
    events: &[SequenceEvent],
    architectural: &HashSet<String>,
    options: &DiagramGenOptions,
) -> Result<DiagramResult, String> {
    // Ensure output directory exists
    fs::create_dir_all(&options.output_dir).map_err(|e| format!("Failed to create output directory: {}", e))?;

    let diagram_opts = options.to_diagram_options();
    let mut result = DiagramResult {
        sequence_path: None,
        class_path: None,
        arch_path: None,
        sequence_content: None,
        class_content: None,
        arch_content: None,
    };

    for diagram_type in &options.diagram_types {
        match diagram_type {
            DiagramType::Sequence | DiagramType::All => {
                let content = generate_sequence_from_events(events, &diagram_opts);
                let path = options.output_dir.join(format!("{}_sequence.md", options.test_name));
                fs::write(&path, &content).map_err(|e| format!("Failed to write sequence diagram: {}", e))?;
                result.sequence_path = Some(path);
                result.sequence_content = Some(content);
            }
            DiagramType::Class => {
                let content = generate_class_from_events(events, &diagram_opts);
                let path = options.output_dir.join(format!("{}_class.md", options.test_name));
                fs::write(&path, &content).map_err(|e| format!("Failed to write class diagram: {}", e))?;
                result.class_path = Some(path);
                result.class_content = Some(content);
            }
            DiagramType::Architecture => {
                let content = generate_arch_from_events(events, architectural, &diagram_opts);
                let path = options.output_dir.join(format!("{}_arch.md", options.test_name));
                fs::write(&path, &content).map_err(|e| format!("Failed to write architecture diagram: {}", e))?;
                result.arch_path = Some(path);
                result.arch_content = Some(content);
            }
        }

        // Handle All type
        if *diagram_type == DiagramType::All {
            // Class diagram
            let content = generate_class_from_events(events, &diagram_opts);
            let path = options.output_dir.join(format!("{}_class.md", options.test_name));
            fs::write(&path, &content).map_err(|e| format!("Failed to write class diagram: {}", e))?;
            result.class_path = Some(path);
            result.class_content = Some(content);

            // Architecture diagram
            let content = generate_arch_from_events(events, architectural, &diagram_opts);
            let path = options.output_dir.join(format!("{}_arch.md", options.test_name));
            fs::write(&path, &content).map_err(|e| format!("Failed to write architecture diagram: {}", e))?;
            result.arch_path = Some(path);
            result.arch_content = Some(content);

            break;
        }
    }

    Ok(result)
}

// ============================================================================
// MD Generator Interface
// ============================================================================

/// Trait for markdown generators that can embed diagrams
pub trait MdDiagramGenerator {
    /// Get the test/document name
    fn name(&self) -> &str;

    /// Get the output directory
    fn output_dir(&self) -> &Path;

    /// Generate and embed a sequence diagram
    fn embed_sequence_diagram(&mut self, events: &[SequenceEvent], options: &DiagramOptions) -> String;

    /// Generate and embed a class diagram
    fn embed_class_diagram(&mut self, events: &[SequenceEvent], options: &DiagramOptions) -> String;

    /// Generate and embed an architecture diagram
    fn embed_arch_diagram(
        &mut self,
        events: &[SequenceEvent],
        architectural: &HashSet<String>,
        options: &DiagramOptions,
    ) -> String;

    /// Write all embedded diagrams to files
    fn write_diagrams(&self) -> Result<Vec<PathBuf>, String>;
}

/// Default markdown diagram generator implementation
pub struct DefaultMdGenerator {
    name: String,
    output_dir: PathBuf,
    diagrams: Vec<(String, String)>, // (filename, content)
}

impl DefaultMdGenerator {
    pub fn new(name: &str, output_dir: &Path) -> Self {
        Self {
            name: name.to_string(),
            output_dir: output_dir.to_path_buf(),
            diagrams: Vec::new(),
        }
    }
}

impl MdDiagramGenerator for DefaultMdGenerator {
    fn name(&self) -> &str {
        &self.name
    }

    fn output_dir(&self) -> &Path {
        &self.output_dir
    }

    fn embed_sequence_diagram(&mut self, events: &[SequenceEvent], options: &DiagramOptions) -> String {
        let content = generate_sequence_from_events(events, options);
        let filename = format!("{}_sequence.md", self.name);
        self.diagrams.push((filename.clone(), content.clone()));
        content
    }

    fn embed_class_diagram(&mut self, events: &[SequenceEvent], options: &DiagramOptions) -> String {
        let content = generate_class_from_events(events, options);
        let filename = format!("{}_class.md", self.name);
        self.diagrams.push((filename.clone(), content.clone()));
        content
    }

    fn embed_arch_diagram(
        &mut self,
        events: &[SequenceEvent],
        architectural: &HashSet<String>,
        options: &DiagramOptions,
    ) -> String {
        let content = generate_arch_from_events(events, architectural, options);
        let filename = format!("{}_arch.md", self.name);
        self.diagrams.push((filename.clone(), content.clone()));
        content
    }

    fn write_diagrams(&self) -> Result<Vec<PathBuf>, String> {
        fs::create_dir_all(&self.output_dir).map_err(|e| format!("Failed to create output directory: {}", e))?;

        let mut paths = Vec::new();
        for (filename, content) in &self.diagrams {
            let path = self.output_dir.join(filename);
            fs::write(&path, content).map_err(|e| format!("Failed to write {}: {}", filename, e))?;
            paths.push(path);
        }

        Ok(paths)
    }
}

// ============================================================================
// CLI Command Implementation
// ============================================================================

/// Parse diagram CLI arguments
pub fn parse_diagram_args(args: &[String]) -> DiagramGenOptions {
    let mut options = DiagramGenOptions::default();
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            "--seq-diagram" | "-s" => {
                options = options.with_type(DiagramType::Sequence);
            }
            "--class-diagram" | "-c" => {
                options = options.with_type(DiagramType::Class);
            }
            "--arch-diagram" | "-a" => {
                options = options.with_type(DiagramType::Architecture);
            }
            "--diagram-all" | "-A" => {
                options = options.with_all_types();
            }
            "--include" | "-i" => {
                i += 1;
                if i < args.len() {
                    for pattern in args[i].split(',') {
                        options = options.with_include(pattern.trim());
                    }
                }
            }
            "--exclude" | "-e" => {
                i += 1;
                if i < args.len() {
                    for pattern in args[i].split(',') {
                        options = options.with_exclude(pattern.trim());
                    }
                }
            }
            "--output" | "-o" => {
                i += 1;
                if i < args.len() {
                    options = options.with_output_dir(Path::new(&args[i]));
                }
            }
            "--name" | "-n" => {
                i += 1;
                if i < args.len() {
                    options.test_name = args[i].clone();
                }
            }
            "--no-timing" => {
                options.include_timing = false;
            }
            "--no-args" => {
                options.include_args = false;
            }
            "--no-returns" => {
                options.include_returns = false;
            }
            "--max-events" => {
                i += 1;
                if i < args.len() {
                    options.max_events = args[i].parse().unwrap_or(0);
                }
            }
            "--from-file" | "-f" => {
                i += 1;
                if i < args.len() {
                    options.from_file = Some(PathBuf::from(&args[i]));
                }
            }
            arg if arg.ends_with(".json") && options.from_file.is_none() => {
                // Positional argument: treat .json file as profile data
                options.from_file = Some(PathBuf::from(arg));
            }
            _ => {}
        }
        i += 1;
    }

    options
}

/// Print diagram CLI help
pub fn print_diagram_help() {
    println!("Diagram Generation");
    println!();
    println!("USAGE:");
    println!("    simple diagram [OPTIONS] [PROFILE_FILE.json]");
    println!();
    println!("INPUT:");
    println!("    -f, --from-file <FILE>  Load profile data from JSON file");
    println!("    <FILE.json>             Positional argument: profile data file");
    println!();
    println!("DIAGRAM TYPES:");
    println!("    -s, --seq-diagram       Generate sequence diagram");
    println!("    -c, --class-diagram     Generate class diagram");
    println!("    -a, --arch-diagram      Generate architecture diagram");
    println!("    -A, --diagram-all       Generate all diagram types");
    println!();
    println!("FILTERS:");
    println!("    -i, --include <PATTERN> Include only matching calls (comma-separated)");
    println!("    -e, --exclude <PATTERN> Exclude matching calls (comma-separated)");
    println!();
    println!("OUTPUT:");
    println!("    -o, --output <DIR>      Output directory (default: target/diagrams)");
    println!("    -n, --name <NAME>       Base name for output files");
    println!();
    println!("FORMATTING:");
    println!("    --no-timing             Exclude timing information");
    println!("    --no-args               Exclude argument values");
    println!("    --no-returns            Exclude return values");
    println!("    --max-events <N>        Maximum events to include");
    println!();
    println!("EXAMPLES:");
    println!("    simple diagram profile.json");
    println!("    simple diagram -f profile.json -A -n my_test");
    println!("    simple diagram profile.json -s --include \"*Service\"");
    println!();
    println!("PROFILE FILE FORMAT:");
    println!("    JSON file with: version, name, events[], architectural_entities[]");
    println!("    Generate with: simple test --seq-diagram my_test.spl");
}
