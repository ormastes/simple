//! Verification commands for Lean verification management.
//!
//! Commands:
//! - `simple verify regenerate` - Regenerate Lean files from verification models
//! - `simple verify check` - Check all proof obligations
//! - `simple verify status` - Show verification status
//! - `simple verify list` - List all proof obligations / inventory

use std::path::Path;

use crate::cli::code_quality::run_verify_quality;
use crate::cli::gen_lean::{known_verification_files, run_gen_lean};

/// Run the verify command.
pub fn run_verify(args: &[String], _gc_log: bool, _gc_off: bool) -> i32 {
    if args.len() < 2 {
        print_verify_help();
        return 0;
    }

    match args[1].as_str() {
        "status" => cmd_status(),
        "regenerate" => cmd_regenerate(),
        "check" => cmd_check(),
        "list" => cmd_list(),
        "quality" => cmd_quality(args),
        "help" | "--help" | "-h" => {
            print_verify_help();
            0
        }
        _ => {
            eprintln!("error: unknown verify subcommand '{}'", args[1]);
            print_verify_help();
            1
        }
    }
}

fn print_verify_help() {
    eprintln!("Simple Verification Tool");
    eprintln!();
    eprintln!("Usage: simple verify <command>");
    eprintln!();
    eprintln!("Commands:");
    eprintln!("  status        Show verification project status");
    eprintln!("  regenerate    Regenerate Lean files from verification models");
    eprintln!("  check         Check Lean artifacts and fail on any sorry");
    eprintln!("  list          List verification artifacts");
    eprintln!("  quality       Audit anti-dummy / anti-stub quality in src/ and test/");
    eprintln!("  help          Show this help message");
    eprintln!();
    eprintln!("Examples:");
    eprintln!("  simple verify status");
    eprintln!("  simple verify regenerate");
    eprintln!("  simple verify check");
    eprintln!("  simple verify quality --all");
}

fn cmd_status() -> i32 {
    println!("Verification Status");
    println!("===================");
    println!();

    let lean_available = check_lean_installed();
    if lean_available {
        println!("Lean 4: ✓ Available");
    } else {
        println!("Lean 4: ✗ Not found (install with: elan install leanprover/lean4:stable)");
    }

    println!();
    println!("Verification Artifacts:");
    let mut present = 0;
    let files = known_verification_files();
    for path in files.iter() {
        let exists = Path::new(path).exists();
        let status = if exists { "✓ OK" } else { "✗ MISSING" };
        if exists {
            present += 1;
        }
        println!("  [{}] {}", status, path);
    }
    println!();
    println!("Artifacts present: {}/{}", present, files.len());
    0
}

fn cmd_regenerate() -> i32 {
    let mut forwarded = vec!["gen-lean".to_string(), "write".to_string(), "--force".to_string()];
    let args: Vec<String> = std::env::args().collect();
    if args.len() > 3 {
        forwarded.extend_from_slice(&args[3..]);
    }
    run_gen_lean(&forwarded)
}

fn cmd_check() -> i32 {
    run_gen_lean(&["gen-lean".to_string(), "verify".to_string()])
}

fn cmd_list() -> i32 {
    println!("Verification Artifact Inventory");
    println!("===============================");
    println!();

    let files = known_verification_files();
    for path in files.iter() {
        println!("  {}", path);
    }
    println!();
    println!("Total artifacts: {}", files.len());
    0
}

fn cmd_quality(args: &[String]) -> i32 {
    run_verify_quality(&args[2..])
}

fn check_lean_installed() -> bool {
    std::process::Command::new("lean")
        .arg("--version")
        .output()
        .map(|output| output.status.success())
        .unwrap_or(false)
}
