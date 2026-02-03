//! CLI entry point and help system for migration commands.

use std::path::PathBuf;

use super::{generics, print, sspec};

/// Run migration command
pub fn run_migrate(args: &[String]) -> i32 {
    // args[0] is "migrate", args[1] is the subcommand
    if args.len() < 2 || args.iter().any(|a| a == "--help" || a == "-h") {
        print_migrate_help();
        return 0;
    }

    let subcommand = &args[1];
    match subcommand.as_str() {
        "--fix-generics" => {
            // Check for --dry-run flag
            let dry_run = args.iter().any(|a| a == "--dry-run" || a == "-n");

            // Find path argument (skip --dry-run flags)
            let path = args
                .iter()
                .skip(2)
                .find(|a| !a.starts_with('-'))
                .map(|s| PathBuf::from(s))
                .unwrap_or_else(|| PathBuf::from("."));

            generics::migrate_generics(&path, dry_run)
        }
        "--fix-print" => {
            // Check for --dry-run flag
            let dry_run = args.iter().any(|a| a == "--dry-run" || a == "-n");

            // Find path argument (skip --dry-run flags)
            let path = args
                .iter()
                .skip(2)
                .find(|a| !a.starts_with('-'))
                .map(|s| PathBuf::from(s))
                .unwrap_or_else(|| PathBuf::from("."));

            print::migrate_print_syntax(&path, dry_run)
        }
        "--fix-sspec-docstrings" => {
            // Check for --dry-run flag
            let dry_run = args.iter().any(|a| a == "--dry-run" || a == "-n");

            // Find path argument (skip --dry-run flags)
            let path = args
                .iter()
                .skip(2)
                .find(|a| !a.starts_with('-'))
                .map(|s| PathBuf::from(s))
                .unwrap_or_else(|| PathBuf::from("."));

            sspec::migrate_sspec_docstrings(&path, dry_run)
        }
        _ => {
            eprintln!("error: unknown migration subcommand: {}", subcommand);
            eprintln!("Run 'simple migrate --help' for usage");
            1
        }
    }
}

fn print_migrate_help() {
    println!("Migration tools for Simple language syntax changes");
    println!();
    println!("Usage:");
    println!("  simple migrate --fix-generics [OPTIONS] [path]");
    println!("  simple migrate --fix-print [OPTIONS] [path]");
    println!("  simple migrate --fix-sspec-docstrings [OPTIONS] [path]");
    println!();
    println!("Migrations:");
    println!("  --fix-generics <path>    Convert [] generic syntax to <>");
    println!("                           Example: List[T] → List<T>");
    println!("                           Processes all .spl files in path");
    println!();
    println!("  --fix-print <path>       Migrate print/println syntax");
    println!("                           println() → print()");
    println!("                           print() → print_raw()");
    println!("                           eprintln() → eprint()");
    println!("                           eprint() → eprint_raw()");
    println!("                           Processes all .spl files in path");
    println!();
    println!("  --fix-sspec-docstrings   Convert print-based SSpec tests to docstrings");
    println!("           <path>          Converts: print('describe...')");
    println!("                           To: describe \"...\":");
    println!("                                   \"\"\"Documentation\"\"\"");
    println!("                           Processes *_spec.spl files only");
    println!();
    println!("Options:");
    println!("  -n, --dry-run           Preview changes without modifying files");
    println!("  -h, --help              Show this help message");
    println!();
    println!("Examples:");
    println!("  simple migrate --fix-generics src/");
    println!("  simple migrate --fix-generics my_file.spl");
    println!("  simple migrate --fix-generics --dry-run src/");
    println!("  simple migrate --fix-print src/std/");
    println!("  simple migrate --fix-print --dry-run .");
    println!("  simple migrate --fix-sspec-docstrings src/std/test/features/");
    println!("  simple migrate --fix-sspec-docstrings --dry-run tests/");
}
