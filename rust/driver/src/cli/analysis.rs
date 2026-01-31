//! Code analysis commands: query generated code, show provenance info.

use simple_parser::{Node, Parser};
use std::fs;
use std::path::{Path, PathBuf};

/// Query for generated code in the codebase
pub fn run_query(args: &[String]) -> i32 {
    // Parse arguments
    let show_generated = args.iter().any(|a| a == "--generated");
    let show_unverified = args.iter().any(|a| a == "--unverified");
    let generated_by_tool = args
        .iter()
        .find(|a| a.starts_with("--generated-by="))
        .and_then(|a| a.strip_prefix("--generated-by="));

    if !show_generated && generated_by_tool.is_none() {
        eprintln!("error: query requires --generated or --generated-by=<tool>");
        eprintln!("Usage:");
        eprintln!("  simple query --generated");
        eprintln!("  simple query --generated --unverified");
        eprintln!("  simple query --generated-by=<tool>");
        return 1;
    }

    // Get the path to search (default to current directory)
    // Skip the first argument (command name "query") and flags
    let search_path = args
        .iter()
        .skip(1)
        .find(|a| !a.starts_with("--"))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."));

    // Collect all .spl files
    let mut spl_files = Vec::new();
    if search_path.is_file() {
        spl_files.push(search_path.clone());
    } else if search_path.is_dir() {
        // Walk directory recursively
        fn walk_dir(dir: &Path, files: &mut Vec<PathBuf>) {
            if let Ok(entries) = fs::read_dir(dir) {
                for entry in entries.flatten() {
                    let path = entry.path();
                    if path.is_file() && path.extension().map_or(false, |e| e == "spl") {
                        files.push(path);
                    } else if path.is_dir() {
                        walk_dir(&path, files);
                    }
                }
            }
        }
        walk_dir(&search_path, &mut spl_files);
    }

    if spl_files.is_empty() {
        eprintln!("error: no .spl files found in {}", search_path.display());
        return 1;
    }

    // Search for generated functions
    let mut found_any = false;
    for file_path in spl_files {
        let source = match fs::read_to_string(&file_path) {
            Ok(s) => s,
            Err(_) => continue,
        };

        let mut parser = Parser::new(&source);
        let module = match parser.parse() {
            Ok(m) => m,
            Err(_) => continue,
        };

        // Search for generated functions
        for item in &module.items {
            if let Node::Function(func) = item {
                if !func.is_generated() {
                    continue;
                }

                let metadata = func.generated_by_metadata();

                // Apply filters
                if let Some(tool_filter) = generated_by_tool {
                    // Check if tool matches
                    let matches_tool = metadata.map_or(false, |args| {
                        args.iter().any(|arg| {
                            if arg.name.as_deref() != Some("tool") {
                                return false;
                            }
                            match &arg.value {
                                simple_parser::Expr::String(s) => s == tool_filter,
                                simple_parser::Expr::FString { parts, .. } => {
                                    // Handle FString with single Literal part
                                    if parts.len() == 1 {
                                        if let simple_parser::FStringPart::Literal(s) = &parts[0] {
                                            return s == tool_filter;
                                        }
                                    }
                                    false
                                }
                                _ => false,
                            }
                        })
                    });
                    if !matches_tool {
                        continue;
                    }
                }

                if show_unverified {
                    // Check if verified flag is false or missing
                    let is_verified = metadata.map_or(false, |args| {
                        args.iter().any(|arg| {
                            arg.name.as_deref() == Some("verified")
                                && matches!(&arg.value, simple_parser::Expr::Bool(true))
                        })
                    });
                    if is_verified {
                        continue;
                    }
                }

                // Print result
                found_any = true;
                println!("{}:{}", file_path.display(), func.name);
            }
        }
    }

    if !found_any {
        println!("No generated functions found.");
    }

    0
}

/// Show information about a function (provenance, metadata)
pub fn run_info(args: &[String]) -> i32 {
    // Parse arguments
    let show_provenance = args.iter().any(|a| a == "--provenance");

    if !show_provenance {
        eprintln!("error: info command currently only supports --provenance");
        eprintln!("Usage: simple info <function> --provenance [file]");
        return 1;
    }

    if args.len() < 2 {
        eprintln!("error: info requires a function name");
        eprintln!("Usage: simple info <function> --provenance [file]");
        return 1;
    }

    let function_name = &args[1];

    // Get the file to search (default to all .spl files in current directory)
    // Skip command name "info", function name, and flags
    let search_path = args
        .iter()
        .skip(3)
        .find(|a| !a.starts_with("--"))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."));

    // Collect all .spl files
    let mut spl_files = Vec::new();
    if search_path.is_file() {
        spl_files.push(search_path.clone());
    } else if search_path.is_dir() {
        // Walk directory recursively
        if let Ok(entries) = fs::read_dir(&search_path) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_file() && path.extension().map_or(false, |e| e == "spl") {
                    spl_files.push(path);
                }
            }
        }
    }

    if spl_files.is_empty() {
        eprintln!("error: no .spl files found in {}", search_path.display());
        return 1;
    }

    // Search for the function
    for file_path in spl_files {
        let source = match fs::read_to_string(&file_path) {
            Ok(s) => s,
            Err(_) => continue,
        };

        let mut parser = Parser::new(&source);
        let module = match parser.parse() {
            Ok(m) => m,
            Err(_) => continue,
        };

        // Search for the function
        for item in &module.items {
            if let Node::Function(func) = item {
                if func.name == *function_name {
                    // Found the function - display provenance
                    println!("Function: {}", func.name);
                    println!("Location: {}", file_path.display());

                    if func.is_generated() {
                        println!("Provenance:");

                        if let Some(metadata) = func.generated_by_metadata() {
                            // Extract and display metadata fields
                            for arg in metadata {
                                if let Some(name) = &arg.name {
                                    let value = match &arg.value {
                                        simple_parser::Expr::String(s) => s.clone(),
                                        simple_parser::Expr::Bool(b) => b.to_string(),
                                        simple_parser::Expr::Integer(i) => i.to_string(),
                                        simple_parser::Expr::FString { parts, .. } => {
                                            // Handle FString with single Literal part
                                            if parts.len() == 1 {
                                                if let simple_parser::FStringPart::Literal(s) = &parts[0] {
                                                    s.clone()
                                                } else {
                                                    format!("{:?}", parts)
                                                }
                                            } else {
                                                format!("{:?}", parts)
                                            }
                                        }
                                        _ => format!("{:?}", arg.value),
                                    };
                                    println!("  {}: {}", name, value);
                                }
                            }
                        } else {
                            println!("  (no metadata)");
                        }
                    } else {
                        println!("Provenance: Not generated (no @generated_by decorator)");
                    }

                    return 0;
                }
            }
        }
    }

    eprintln!("error: function '{}' not found", function_name);
    1
}
