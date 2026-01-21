// Standalone sspec documentation generator
// Usage: cargo run --bin gen-sspec-docs -- tests/system/*_spec.spl

use std::env;
use std::path::PathBuf;
use simple_driver::cli::sspec_docgen;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: gen-sspec-docs <spec_file>...");
        std::process::exit(1);
    }

    let spec_files: Vec<PathBuf> = args[1..].iter().map(PathBuf::from).collect();
    let output_dir = PathBuf::from("doc/spec");

    match sspec_docgen::generate_sspec_docs(&spec_files, &output_dir) {
        Ok(stats) => {
            println!(
                "\n✓ Generated {} docs ({} complete, {} stubs)",
                stats.total_specs, stats.specs_with_docs, stats.specs_without_docs
            );
        }
        Err(e) => {
            eprintln!("✗ Failed to generate documentation: {}", e);
            std::process::exit(1);
        }
    }
}
