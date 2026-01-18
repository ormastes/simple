//! Simple Context Pack Generator - Standalone Tool
//!
//! Extracts minimal context for LLM consumption (#890-893)

use simple_compiler::api_surface::ApiSurface;
use simple_compiler::context_pack::ContextPack;
use simple_parser::Parser;
use std::env;
use std::fs;
use std::path::PathBuf;
use std::process;

fn print_help() {
    eprintln!("Simple Context Pack Generator");
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  simple-context <file.spl> [target] [options]");
    eprintln!();
    eprintln!("Arguments:");
    eprintln!("  <file.spl>  Source file to analyze");
    eprintln!("  [target]    Target function/module (default: file name)");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  --format=<fmt>  Output format: json, markdown, text (default: markdown)");
    eprintln!("  --json          Shorthand for --format=json");
    eprintln!("  --text          Shorthand for --format=text");
    eprintln!("  -o <file>       Output to file instead of stdout");
    eprintln!("  --stats         Show context reduction statistics");
    eprintln!("  -h, --help      Show this help");
    eprintln!();
    eprintln!("Examples:");
    eprintln!("  simple-context app.spl");
    eprintln!("  simple-context app.spl UserService --json");
    eprintln!("  simple-context app.spl calculate --format=markdown -o context.md");
    eprintln!();
    eprintln!("Features:");
    eprintln!("  - 90% reduction in LLM context tokens");
    eprintln!("  - Extracts only symbols used by target");
    eprintln!("  - Multiple export formats (JSON, Markdown, Text)");
}

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 || args.iter().any(|a| a == "-h" || a == "--help") {
        print_help();
        process::exit(if args.len() < 2 { 1 } else { 0 });
    }

    // Parse arguments
    let source_path = PathBuf::from(&args[1]);
    let target = args
        .get(2)
        .map(|s| s.as_str())
        .unwrap_or_else(|| source_path.file_stem().and_then(|s| s.to_str()).unwrap_or("main"));

    // Parse flags
    let mut format = "markdown";
    let mut output_file: Option<PathBuf> = None;
    let mut show_stats = false;

    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--json" => format = "json",
            "--text" => format = "text",
            "--stats" => show_stats = true,
            "-o" => {
                if let Some(path) = args.get(i + 1) {
                    output_file = Some(PathBuf::from(path));
                    i += 1;
                }
            }
            arg if arg.starts_with("--format=") => {
                format = arg.strip_prefix("--format=").unwrap();
            }
            _ => {}
        }
        i += 1;
    }

    // Read source file
    let source = match fs::read_to_string(&source_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", source_path.display(), e);
            process::exit(1);
        }
    };

    // Parse source
    let mut parser = Parser::new(&source);
    let module = match parser.parse() {
        Ok(m) => m,
        Err(e) => {
            eprintln!("error: parse failed: {}", e);
            process::exit(1);
        }
    };

    // Create API surface from the parsed module
    let module_name = source_path.file_stem().and_then(|s| s.to_str()).unwrap_or("module");
    let api_surface = ApiSurface::from_nodes(module_name, &module.items);

    // Generate context pack
    let context = ContextPack::from_target(target, &module.items, &api_surface);

    // Show stats if requested
    if show_stats {
        let full_count = module.items.len();
        eprintln!("Context Statistics:");
        eprintln!("  Full module symbols: {}", full_count);
        eprintln!("  Extracted symbols:   {}", context.symbol_count);
        eprintln!("  Reduction:           {:.1}%", context.token_savings(full_count));
        eprintln!();
    }

    // Generate output
    let output = match format {
        "json" => context.to_json().unwrap_or_else(|e| {
            eprintln!("error: failed to generate JSON: {}", e);
            process::exit(1);
        }),
        "text" => context.to_text(),
        "markdown" | _ => context.to_markdown(),
    };

    // Write output
    match output_file {
        Some(path) => {
            if let Err(e) = fs::write(&path, output) {
                eprintln!("error: cannot write {}: {}", path.display(), e);
                process::exit(1);
            }
            eprintln!("Context written to {}", path.display());
        }
        None => {
            println!("{}", output);
        }
    }
}
