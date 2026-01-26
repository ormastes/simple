//! Miscellaneous command handlers (diagram, lock, run, etc.)

use std::path::PathBuf;
use crate::cli::diagram_gen::{generate_diagrams_from_events, parse_diagram_args, print_diagram_help};
use crate::cli::lock;

/// Handle 'diagram' command - generate UML diagrams from profile data
pub fn handle_diagram(args: &[String]) -> i32 {
    // Check for help
    if args.iter().any(|a| a == "-h" || a == "--help") {
        print_diagram_help();
        return 0;
    }

    // Parse diagram generation options
    let diagram_args: Vec<String> = args[1..].to_vec();
    let options = parse_diagram_args(&diagram_args);

    // Check if we have a profile file to load
    if let Some(ref profile_path) = options.from_file {
        // Load profile data from file
        match simple_compiler::runtime_profile::ProfileData::load_from_file(profile_path) {
            Ok(profile_data) => {
                println!(
                    "Loaded profile: {} ({} events)",
                    profile_data.name,
                    profile_data.events.len()
                );

                // Generate diagrams from the loaded profile data
                let architectural = profile_data.get_architectural_entities();
                match generate_diagrams_from_events(profile_data.get_events(), &architectural, &options) {
                    Ok(result) => {
                        if let Some(path) = result.sequence_path {
                            println!("  Sequence diagram: {}", path.display());
                        }
                        if let Some(path) = result.class_path {
                            println!("  Class diagram: {}", path.display());
                        }
                        if let Some(path) = result.arch_path {
                            println!("  Architecture diagram: {}", path.display());
                        }
                        println!("Diagrams generated successfully.");
                        0
                    }
                    Err(e) => {
                        eprintln!("error: failed to generate diagrams: {}", e);
                        1
                    }
                }
            }
            Err(e) => {
                eprintln!("error: {}", e);
                1
            }
        }
    } else {
        // No profile file specified - show usage help
        print_diagram_usage(&options);
        0
    }
}

fn print_diagram_usage(options: &crate::cli::diagram_gen::DiagramGenOptions) {
    println!("Diagram generation options:");
    println!("  Types: {:?}", options.diagram_types);
    println!("  Output: {}", options.output_dir.display());
    println!("  Name: {}", options.test_name);
    if !options.include_patterns.is_empty() {
        println!("  Include: {:?}", options.include_patterns);
    }
    if !options.exclude_patterns.is_empty() {
        println!("  Exclude: {:?}", options.exclude_patterns);
    }

    println!();
    println!("No profile file specified. Usage:");
    println!("  simple diagram <profile.json>           Load and generate diagrams");
    println!("  simple diagram -f <file> -A             Generate all diagram types");
    println!();
    println!("To record profile data, use:");
    println!("  simple test --seq-diagram my_test.spl");
}

/// Handle 'lock' command - manage lock files
pub fn handle_lock(args: &[String]) -> i32 {
    let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let check_only = args.iter().any(|a| a == "--check");
    let info_only = args.iter().any(|a| a == "--info");

    if info_only {
        lock::lock_info(&dir)
    } else if check_only {
        lock::check_lock(&dir)
    } else {
        lock::generate_lock(&dir)
    }
}

/// Handle 'run' command - explicit run command for compatibility
pub fn handle_run(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    if args.len() < 2 {
        eprintln!("error: run requires a file");
        return 1;
    }
    let path = PathBuf::from(&args[1]);
    crate::cli::basic::run_file(&path, gc_log, gc_off)
}

/// Handle 'brief' command - LLM-friendly code overview
pub fn handle_brief(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    // Skip the command name ("brief") and pass remaining args
    let brief_args: Vec<String> = args[1..].iter()
        .map(|a| format!("\"{}\"", a.replace("\"", "\\\"")))
        .collect();

    let code = format!(
        r#"use tooling.brief_view.{{run_brief}}

fn main() -> i64:
    val args = [{}]
    run_brief(args) as i64"#,
        brief_args.join(", ")
    );

    crate::cli::basic::run_code(&code, gc_log, gc_off)
}
