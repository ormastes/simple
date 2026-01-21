//! Verification commands - Lean verification management.
//!
//! Commands:
//! - `simple verify regenerate` - Regenerate Lean files from models
//! - `simple verify check` - Check all proof obligations
//! - `simple verify status` - Show verification status
//! - `simple verify list` - List all proof obligations
//!
//! Note: This is a wrapper that will eventually call the Simple verify app (simple/app/verify/main.spl)
//! when Phase 6 self-hosting is complete. For now, it provides basic status information.

use std::fs;
use std::path::Path;

/// Run the verify command
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
    eprintln!("  check         Check all proof obligations");
    eprintln!("  list          List all proof obligations");
    eprintln!("  help          Show this help message");
    eprintln!();
    eprintln!("Examples:");
    eprintln!("  simple verify status");
    eprintln!("  simple verify regenerate");
    eprintln!("  simple verify check");
    eprintln!();
    eprintln!("Note: For full functionality, use:");
    eprintln!("  simple gen-lean generate    # Generate Lean files from Simple code");
    eprintln!("  simple gen-lean verify      # Run Lean proof checker");
}

fn cmd_status() -> i32 {
    println!("Verification Status");
    println!("===================");
    println!();

    // Check Lean availability
    let lean_available = check_lean_installed();
    if lean_available {
        println!("Lean 4: ✓ Available");
    } else {
        println!("Lean 4: ✗ Not found (install with: elan install leanprover/lean4:stable)");
    }

    println!();

    // List verification projects
    let projects = vec![
        ("memory_capabilities", "Reference capability verification"),
        ("memory_model_drf", "SC-DRF memory model verification"),
        ("type_inference_compile", "Type inference proofs"),
        ("async_compile", "Async effect tracking"),
        ("gc_manual_borrow", "GC safety proofs"),
        ("nogc_compile", "NoGC instruction verification"),
        ("module_resolution", "Module resolution verification"),
        ("visibility_export", "Visibility and export verification"),
        ("monomorphization", "Generic monomorphization correctness"),
        ("effect_system", "Effect inference verification"),
        ("macro_auto_import", "Macro system verification"),
        ("pattern_matching", "Pattern matching exhaustiveness"),
        ("static_dispatch_verification", "Static dispatch correctness"),
    ];

    println!("Verification Projects:");
    for (name, description) in projects {
        let dir = format!("verification/{}", name);
        let status = if Path::new(&dir).exists() {
            "✓ OK"
        } else {
            "✗ MISSING"
        };
        println!("  [{}] {} - {}", status, name, description);
    }

    println!();
    println!("Use 'simple gen-lean verify' to run Lean proof checker on all projects.");

    0
}

fn cmd_regenerate() -> i32 {
    eprintln!("Note: Full regeneration functionality requires Phase 6 self-hosting completion.");
    eprintln!("Use 'simple gen-lean generate' to generate Lean files from Simple code.");
    eprintln!();
    eprintln!("Available gen-lean commands:");
    eprintln!("  simple gen-lean generate           # Generate all Lean files");
    eprintln!("  simple gen-lean compare            # Compare with existing");
    eprintln!("  simple gen-lean write              # Write generated files");
    1
}

fn cmd_check() -> i32 {
    eprintln!("Checking proof obligations...");
    eprintln!();
    eprintln!("Note: Full proof checking requires Phase 6 self-hosting completion.");
    eprintln!("Use 'simple gen-lean verify' to run Lean proof checker.");
    1
}

fn cmd_list() -> i32 {
    println!("Proof Obligations");
    println!("=================");
    println!();
    println!("Note: Full obligation listing requires Phase 6 self-hosting completion.");
    println!();
    println!("To see verification project status, use:");
    println!("  simple verify status");
    1
}

fn check_lean_installed() -> bool {
    std::process::Command::new("lean")
        .arg("--version")
        .output()
        .map(|output| output.status.success())
        .unwrap_or(false)
}
