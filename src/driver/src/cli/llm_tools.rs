//! LLM-friendly tools: context extraction, semantic diff, MCP generation.

use simple_compiler::api_surface::ApiSurface;
use simple_compiler::context_pack::ContextPack;
use simple_compiler::mcp::{ExpandWhat, McpGenerator, McpTools};
use simple_compiler::semantic_diff::SemanticDiffer;
use simple_compiler::text_diff::TextDiff;
use simple_parser::Parser;
use std::fs;
use std::path::PathBuf;

/// Extract context pack from a source file
pub fn run_context(args: &[String]) -> i32 {
    // Parse arguments
    if args.len() < 2 {
        eprintln!("error: context requires a source file");
        eprintln!("Usage: simple context <file.spl> [target] [--minimal] [--json] [--markdown]");
        return 1;
    }

    let path = PathBuf::from(&args[1]);
    let target = args
        .get(2)
        .filter(|s| !s.starts_with("--"))
        .map(|s| s.as_str());
    let minimal = args.iter().any(|a| a == "--minimal");
    let json_output = args.iter().any(|a| a == "--json");
    let markdown_output = args.iter().any(|a| a == "--markdown");

    // Read file
    let source = match fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", path.display(), e);
            return 1;
        }
    };

    // Parse
    let mut parser = Parser::new(&source);
    let module = match parser.parse() {
        Ok(m) => m,
        Err(e) => {
            eprintln!("error: parse failed: {}", e);
            return 1;
        }
    };

    // Build API surface from module
    let api_surface = ApiSurface::from_nodes(&path.display().to_string(), &module.items);

    // Extract context pack
    let target_name = target.unwrap_or("main");
    let pack = if minimal {
        ContextPack::from_target_minimal(target_name, &module.items, &api_surface)
    } else {
        ContextPack::from_target(target_name, &module.items, &api_surface)
    };

    // Output in requested format
    if json_output {
        match pack.to_json() {
            Ok(json) => {
                println!("{}", json);
                0
            }
            Err(e) => {
                eprintln!("error: failed to generate JSON: {}", e);
                1
            }
        }
    } else if markdown_output {
        println!("{}", pack.to_markdown());
        0
    } else {
        // Default: plain text
        println!("{}", pack.to_text());

        // Show stats
        let full_count = api_surface.functions.len()
            + api_surface.structs.len()
            + api_surface.classes.len()
            + api_surface.enums.len()
            + api_surface.traits.len();
        if full_count > 0 {
            let savings = pack.token_savings(full_count);
            eprintln!();
            eprintln!("Context reduction: {:.1}%", savings);
            eprintln!(
                "Symbols: {} / {} (extracted / total)",
                pack.symbol_count, full_count
            );
        }
        0
    }
}

/// Run semantic diff between two source files
pub fn run_diff(args: &[String]) -> i32 {
    // Parse arguments
    if args.len() < 3 {
        eprintln!("error: diff requires two source files");
        eprintln!("Usage: simple diff <old.spl> <new.spl> [--semantic] [--json]");
        return 1;
    }

    let old_path = PathBuf::from(&args[1]);
    let new_path = PathBuf::from(&args[2]);
    let semantic = args.iter().any(|a| a == "--semantic");
    let json_output = args.iter().any(|a| a == "--json");

    // Read old file
    let old_source = match fs::read_to_string(&old_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", old_path.display(), e);
            return 1;
        }
    };

    // Read new file
    let new_source = match fs::read_to_string(&new_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", new_path.display(), e);
            return 1;
        }
    };

    // Parse old file
    if semantic {
        // Semantic diff (AST-based) - requires parsing
        let mut old_parser = Parser::new(&old_source);
        let old_module = match old_parser.parse() {
            Ok(m) => m,
            Err(e) => {
                eprintln!("error: parse failed in {}: {}", old_path.display(), e);
                return 1;
            }
        };

        // Parse new file
        let mut new_parser = Parser::new(&new_source);
        let new_module = match new_parser.parse() {
            Ok(m) => m,
            Err(e) => {
                eprintln!("error: parse failed in {}: {}", new_path.display(), e);
                return 1;
            }
        };

        let differ =
            SemanticDiffer::new(format!("{} -> {}", old_path.display(), new_path.display()));
        let diff = differ.diff_modules(&old_module, &new_module);

        if json_output {
            match SemanticDiffer::format_json(&diff) {
                Ok(json) => {
                    println!("{}", json);
                    0
                }
                Err(e) => {
                    eprintln!("error: failed to format JSON: {}", e);
                    1
                }
            }
        } else {
            println!("{}", SemanticDiffer::format_text(&diff));
            0
        }
    } else {
        // Text-based diff (line-by-line using LCS algorithm)
        let diff = TextDiff::new(&old_source, &new_source);

        if json_output {
            let json = serde_json::json!({
                "old_file": old_path.display().to_string(),
                "new_file": new_path.display().to_string(),
                "additions": diff.additions(),
                "deletions": diff.deletions(),
                "hunks": diff.hunks.len(),
            });
            println!("{}", serde_json::to_string_pretty(&json).unwrap());
            0
        } else {
            let output = diff.format_unified(
                &old_path.display().to_string(),
                &new_path.display().to_string(),
                3,
            );
            print!("{}", output);
            0
        }
    }
}

/// Generate MCP (minimal code preview) from a source file
pub fn run_mcp(args: &[String]) -> i32 {
    // Parse arguments
    if args.len() < 2 {
        eprintln!("error: mcp requires a source file");
        eprintln!(
            "Usage: simple mcp <file.spl> [--expand <symbol>] [--search <query>] [--show-coverage]"
        );
        return 1;
    }

    let path = PathBuf::from(&args[1]);
    let expand_symbol = args
        .iter()
        .position(|a| a == "--expand")
        .and_then(|i| args.get(i + 1))
        .map(|s| s.as_str());
    let search_query = args
        .iter()
        .position(|a| a == "--search")
        .and_then(|i| args.get(i + 1))
        .map(|s| s.as_str());
    let show_coverage = args.iter().any(|a| a == "--show-coverage");

    // Read file
    let source = match fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", path.display(), e);
            return 1;
        }
    };

    // Parse
    let mut parser = Parser::new(&source);
    let nodes = match parser.parse() {
        Ok(nodes) => nodes,
        Err(e) => {
            eprintln!("error: parse failed: {}", e);
            return 1;
        }
    };

    // Generate MCP output
    if let Some(query) = search_query {
        // Search mode
        let tools = McpTools::new();
        let results = tools.search(&nodes.items, query, true);
        if results.is_empty() {
            eprintln!("No symbols found matching '{}'", query);
            return 1;
        } else {
            println!("Found {} symbol(s):", results.len());
            for result in results {
                println!("  {}", result);
            }
            return 0;
        }
    } else if let Some(symbol) = expand_symbol {
        // Expand mode
        let tools = McpTools::new();
        match tools.expand_at(&nodes.items, symbol, ExpandWhat::All) {
            Ok(json) => {
                println!("{}", json);
                0
            }
            Err(e) => {
                eprintln!("error: failed to generate MCP: {}", e);
                1
            }
        }
    } else {
        // Default collapsed mode
        let mut generator = McpGenerator::new();
        if show_coverage {
            generator = generator.show_coverage(true);
        }
        let output = generator.generate(&nodes.items);
        match serde_json::to_string_pretty(&output) {
            Ok(json) => {
                println!("{}", json);
                0
            }
            Err(e) => {
                eprintln!("error: failed to generate MCP: {}", e);
                1
            }
        }
    }
}
