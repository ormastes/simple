//! i18n (Internationalization) commands for Simple language.
//!
//! Provides tools for extracting i18n strings and generating locale files.

use std::fs;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

use simple_compiler::i18n::{ExtractionResult, I18nExtractor, LocaleGenerator};
use simple_parser::Parser;

/// Run i18n command
pub fn run_i18n(args: &[String]) -> i32 {
    // args[0] is "i18n", args[1] is the subcommand
    if args.len() < 2 || args.iter().any(|a| a == "--help" || a == "-h") {
        print_i18n_help();
        return 0;
    }

    let subcommand = &args[1];
    match subcommand.as_str() {
        "extract" => {
            // Find path argument
            let path = args
                .iter()
                .skip(2)
                .find(|a| !a.starts_with('-'))
                .map(|s| PathBuf::from(s))
                .unwrap_or_else(|| PathBuf::from("src"));

            // Find output directory
            let output = args
                .iter()
                .position(|a| a == "-o" || a == "--output")
                .and_then(|i| args.get(i + 1))
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from("i18n"));

            extract_i18n_strings(&path, &output)
        }
        "generate" => {
            if args.len() < 3 {
                eprintln!("error: i18n generate requires a locale code");
                eprintln!("Usage: simple i18n generate <locale> [-o <output>]");
                return 1;
            }

            let locale = &args[2];

            // Find path argument for extraction
            let path = args
                .iter()
                .skip(3)
                .find(|a| !a.starts_with('-') && !a.starts_with("--"))
                .map(|s| PathBuf::from(s))
                .unwrap_or_else(|| PathBuf::from("src"));

            // Find output directory
            let output = args
                .iter()
                .position(|a| a == "-o" || a == "--output")
                .and_then(|i| args.get(i + 1))
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from("i18n"));

            generate_locale_template(locale, &path, &output)
        }
        _ => {
            eprintln!("error: unknown i18n subcommand: {}", subcommand);
            eprintln!("Run 'simple i18n --help' for usage");
            1
        }
    }
}

fn print_i18n_help() {
    println!("Internationalization tools for Simple language");
    println!();
    println!("Usage:");
    println!("  simple i18n extract [OPTIONS] [path]");
    println!("  simple i18n generate <locale> [OPTIONS] [path]");
    println!();
    println!("Commands:");
    println!("  extract              Extract i18n strings from source files");
    println!("  generate <locale>    Generate a locale template file");
    println!();
    println!("Options:");
    println!("  -o, --output <dir>   Output directory (default: i18n/)");
    println!("  path                 Source path to scan (default: src/)");
    println!();
    println!("Examples:");
    println!("  simple i18n extract                    # Extract from src/ to i18n/");
    println!("  simple i18n extract app/ -o locale/    # Extract from app/ to locale/");
    println!("  simple i18n generate ko-KR             # Generate Korean locale template");
    println!("  simple i18n generate es-ES -o locale/  # Generate Spanish locale template");
    println!();
    println!("i18n String Syntax:");
    println!("  Name_\"default text\"                    # Named string literal");
    println!("  Name_\"Hello {{user}}!\"{{user: name}}     # Template with args");
    println!();
    println!("Generated Files:");
    println!("  __init__.spl            # Default locale (extracted strings)");
    println!("  __init__.<locale>.spl   # Locale-specific translations");
}

/// Extract i18n strings from source files
fn extract_i18n_strings(path: &Path, output: &Path) -> i32 {
    println!("Extracting i18n strings from {}...", path.display());

    let mut extractor = I18nExtractor::new();
    let mut file_count = 0;
    let mut error_count = 0;

    // Walk the source directory
    for entry in WalkDir::new(path).follow_links(true).into_iter().filter_map(|e| e.ok()) {
        let path = entry.path();

        // Only process .spl files
        if path.extension().map(|e| e == "spl").unwrap_or(false) {
            file_count += 1;

            match fs::read_to_string(path) {
                Ok(content) => {
                    let mut parser = Parser::new(&content);
                    match parser.parse() {
                        Ok(module) => {
                            extractor.extract_module(&module, path.to_path_buf());
                        }
                        Err(e) => {
                            eprintln!("  warning: parse error in {}: {}", path.display(), e);
                            error_count += 1;
                        }
                    }
                }
                Err(e) => {
                    eprintln!("  warning: failed to read {}: {}", path.display(), e);
                    error_count += 1;
                }
            }
        }
    }

    let result = extractor.finish();

    // Print warnings
    for warning in &result.warnings {
        eprintln!("  {}", warning);
    }

    // Generate locale files
    let generator = LocaleGenerator::new(output.to_path_buf());
    match generator.generate(&result) {
        Ok(files) => {
            println!();
            println!(
                "Extracted {} i18n strings from {} files",
                result.strings.len(),
                file_count
            );

            for file in &files {
                println!("  Generated: {}", file.display());
            }

            if error_count > 0 {
                println!();
                println!("  {} files had errors", error_count);
            }

            0
        }
        Err(e) => {
            eprintln!("error: failed to generate locale files: {}", e);
            1
        }
    }
}

/// Generate a locale template for a specific locale
fn generate_locale_template(locale: &str, path: &Path, output: &Path) -> i32 {
    println!("Generating {} locale template from {}...", locale, path.display());

    let mut extractor = I18nExtractor::new();
    let mut file_count = 0;

    // Walk the source directory
    for entry in WalkDir::new(path).follow_links(true).into_iter().filter_map(|e| e.ok()) {
        let path = entry.path();

        // Only process .spl files
        if path.extension().map(|e| e == "spl").unwrap_or(false) {
            file_count += 1;

            if let Ok(content) = fs::read_to_string(path) {
                let mut parser = Parser::new(&content);
                if let Ok(module) = parser.parse() {
                    extractor.extract_module(&module, path.to_path_buf());
                }
            }
        }
    }

    let result = extractor.finish();

    // Generate locale template
    let generator = LocaleGenerator::new(output.to_path_buf());
    match generator.generate_locale_template(locale, &result) {
        Ok(file) => {
            println!();
            println!("Generated locale template: {}", file.display());
            println!("  {} strings from {} files", result.strings.len(), file_count);
            println!();
            println!("Next steps:");
            println!("  1. Edit {} and translate the values", file.display());
            println!("  2. Keep the val names unchanged (they are the keys)");
            println!("  3. Import the locale file in your application");

            0
        }
        Err(e) => {
            eprintln!("error: failed to generate locale template: {}", e);
            1
        }
    }
}
