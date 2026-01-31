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
    let target = args.get(2).filter(|s| !s.starts_with("--")).map(|s| s.as_str());
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
            eprintln!("Symbols: {} / {} (extracted / total)", pack.symbol_count, full_count);
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

        let differ = SemanticDiffer::new(format!("{} -> {}", old_path.display(), new_path.display()));
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
            let output = diff.format_unified(&old_path.display().to_string(), &new_path.display().to_string(), 3);
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
        eprintln!("Usage: simple mcp <file.spl> [--expand <symbol>] [--search <query>] [--show-coverage]");
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
        let mut generator = McpGenerator::new().public_only(false);
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

/// Constraint collected from the AST
#[derive(Debug, Clone)]
struct TypeConstraint {
    kind: ConstraintKind,
    name: String,
    type_info: String,
    location: String,
}

#[derive(Debug, Clone)]
enum ConstraintKind {
    FunctionSignature,
    VariableDecl,
    FieldType,
    TraitBound,
    ReturnType,
    ParameterType,
}

impl ConstraintKind {
    fn as_str(&self) -> &'static str {
        match self {
            ConstraintKind::FunctionSignature => "function_signature",
            ConstraintKind::VariableDecl => "variable_decl",
            ConstraintKind::FieldType => "field_type",
            ConstraintKind::TraitBound => "trait_bound",
            ConstraintKind::ReturnType => "return_type",
            ConstraintKind::ParameterType => "parameter_type",
        }
    }
}

/// Collect type constraints from AST
fn collect_constraints(items: &[simple_parser::ast::Node]) -> Vec<TypeConstraint> {
    use simple_parser::ast::*;
    let mut constraints = Vec::new();

    for item in items {
        match item {
            Node::Function(func) => {
                // Collect function signature constraint
                let params_str: Vec<String> = func
                    .params
                    .iter()
                    .map(|p| format!("{}: {}", p.name, type_to_string_opt(&p.ty)))
                    .collect();
                let ret_str = func
                    .return_type
                    .as_ref()
                    .map(|t| type_to_string(t))
                    .unwrap_or_else(|| "()".to_string());

                constraints.push(TypeConstraint {
                    kind: ConstraintKind::FunctionSignature,
                    name: func.name.clone(),
                    type_info: format!("({}) -> {}", params_str.join(", "), ret_str),
                    location: format!("line {}", func.span.line),
                });

                // Collect parameter constraints
                for param in &func.params {
                    if param.ty.is_some() {
                        constraints.push(TypeConstraint {
                            kind: ConstraintKind::ParameterType,
                            name: format!("{}::{}", func.name, param.name),
                            type_info: type_to_string_opt(&param.ty),
                            location: format!("line {}", func.span.line),
                        });
                    }
                }

                // Collect return type constraint
                if let Some(ref ret) = func.return_type {
                    constraints.push(TypeConstraint {
                        kind: ConstraintKind::ReturnType,
                        name: func.name.clone(),
                        type_info: type_to_string(ret),
                        location: format!("line {}", func.span.line),
                    });
                }

                // Collect trait bounds from where clause
                for bound in &func.where_clause {
                    let bounds_str: Vec<String> = bound.bounds.iter().map(|b| type_to_string(b)).collect();
                    constraints.push(TypeConstraint {
                        kind: ConstraintKind::TraitBound,
                        name: format!("{}::{}", func.name, bound.type_param),
                        type_info: bounds_str.join(" + "),
                        location: format!("line {}", func.span.line),
                    });
                }
            }
            Node::Struct(s) => {
                for field in &s.fields {
                    constraints.push(TypeConstraint {
                        kind: ConstraintKind::FieldType,
                        name: format!("{}::{}", s.name, field.name),
                        type_info: type_to_string(&field.ty),
                        location: format!("line {}", s.span.line),
                    });
                }
            }
            Node::Class(c) => {
                for field in &c.fields {
                    constraints.push(TypeConstraint {
                        kind: ConstraintKind::FieldType,
                        name: format!("{}::{}", c.name, field.name),
                        type_info: type_to_string(&field.ty),
                        location: format!("line {}", c.span.line),
                    });
                }
                // Collect methods
                for method in &c.methods {
                    let params_str: Vec<String> = method
                        .params
                        .iter()
                        .map(|p| format!("{}: {}", p.name, type_to_string_opt(&p.ty)))
                        .collect();
                    let ret_str = method
                        .return_type
                        .as_ref()
                        .map(|t| type_to_string(t))
                        .unwrap_or_else(|| "()".to_string());

                    constraints.push(TypeConstraint {
                        kind: ConstraintKind::FunctionSignature,
                        name: format!("{}::{}", c.name, method.name),
                        type_info: format!("({}) -> {}", params_str.join(", "), ret_str),
                        location: format!("line {}", method.span.line),
                    });
                }
            }
            Node::Trait(t) => {
                for method in &t.methods {
                    let params_str: Vec<String> = method
                        .params
                        .iter()
                        .map(|p| format!("{}: {}", p.name, type_to_string_opt(&p.ty)))
                        .collect();
                    let ret_str = method
                        .return_type
                        .as_ref()
                        .map(|t| type_to_string(t))
                        .unwrap_or_else(|| "()".to_string());

                    constraints.push(TypeConstraint {
                        kind: ConstraintKind::FunctionSignature,
                        name: format!("{}::{}", t.name, method.name),
                        type_info: format!("({}) -> {}", params_str.join(", "), ret_str),
                        location: format!("line {}", method.span.line),
                    });
                }
            }
            Node::Let(let_stmt) => {
                if let_stmt.ty.is_some() {
                    constraints.push(TypeConstraint {
                        kind: ConstraintKind::VariableDecl,
                        name: pattern_to_string(&let_stmt.pattern),
                        type_info: type_to_string_opt(&let_stmt.ty),
                        location: format!("line {}", let_stmt.span.line),
                    });
                }
            }
            Node::Impl(impl_block) => {
                for method in &impl_block.methods {
                    let params_str: Vec<String> = method
                        .params
                        .iter()
                        .map(|p| format!("{}: {}", p.name, type_to_string_opt(&p.ty)))
                        .collect();
                    let ret_str = method
                        .return_type
                        .as_ref()
                        .map(|t| type_to_string(t))
                        .unwrap_or_else(|| "()".to_string());

                    constraints.push(TypeConstraint {
                        kind: ConstraintKind::FunctionSignature,
                        name: format!("{}::{}", type_to_string(&impl_block.target_type), method.name),
                        type_info: format!("({}) -> {}", params_str.join(", "), ret_str),
                        location: format!("line {}", method.span.line),
                    });
                }
            }
            _ => {}
        }
    }

    constraints
}

/// Convert Pattern to string representation
fn pattern_to_string(pat: &simple_parser::ast::Pattern) -> String {
    use simple_parser::ast::Pattern;
    match pat {
        Pattern::Identifier(name) => name.clone(),
        Pattern::Tuple(patterns) => {
            let inner: Vec<String> = patterns.iter().map(|p| pattern_to_string(p)).collect();
            format!("({})", inner.join(", "))
        }
        Pattern::Wildcard => "_".to_string(),
        _ => format!("{:?}", pat),
    }
}

/// Convert Type to string representation
fn type_to_string(ty: &simple_parser::ast::Type) -> String {
    use simple_parser::ast::Type;
    match ty {
        Type::Simple(name) => name.clone(),
        Type::Generic { name, args } => {
            let args_str: Vec<String> = args.iter().map(|a| type_to_string(a)).collect();
            format!("{}<{}>", name, args_str.join(", "))
        }
        Type::Tuple(types) => {
            let types_str: Vec<String> = types.iter().map(|t| type_to_string(t)).collect();
            format!("({})", types_str.join(", "))
        }
        Type::Array { element, size } => {
            let elem_str = type_to_string(element);
            match size {
                Some(_) => format!("[{}; N]", elem_str),
                None => format!("[{}]", elem_str),
            }
        }
        Type::Function { params, ret } => {
            let params_str: Vec<String> = params.iter().map(|p| type_to_string(p)).collect();
            let ret_str = ret
                .as_ref()
                .map(|r| type_to_string(r))
                .unwrap_or_else(|| "()".to_string());
            format!("fn({}) -> {}", params_str.join(", "), ret_str)
        }
        Type::Optional(inner) => format!("{}?", type_to_string(inner)),
        Type::SelfType => "Self".to_string(),
        _ => format!("{:?}", ty),
    }
}

/// Convert Option<Type> to string representation
fn type_to_string_opt(ty: &Option<simple_parser::ast::Type>) -> String {
    match ty {
        None => "_".to_string(),
        Some(t) => type_to_string(t),
    }
}

/// Run constraint analysis on a source file
pub fn run_constr(args: &[String]) -> i32 {
    if args.len() < 2 {
        eprintln!("error: constr requires a source file");
        eprintln!("Usage: simple constr <file.spl> [--json] [--verbose]");
        eprintln!();
        eprintln!("Constraint Analysis:");
        eprintln!("  Analyzes type constraints and inference in the source file.");
        eprintln!();
        eprintln!("Options:");
        eprintln!("  --json      Output as JSON");
        eprintln!("  --verbose   Show detailed constraint information");
        return 1;
    }

    let path = PathBuf::from(&args[1]);
    let json_output = args.iter().any(|a| a == "--json");
    let verbose = args.iter().any(|a| a == "--verbose");

    // Read source file
    let source = match fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", path.display(), e);
            return 1;
        }
    };

    // Parse source
    let mut parser = Parser::new(&source);
    let ast = match parser.parse() {
        Ok(ast) => ast,
        Err(e) => {
            eprintln!("error: parse error: {:?}", e);
            return 1;
        }
    };

    // Collect constraints from AST
    let constraints = collect_constraints(&ast.items);

    if json_output {
        // Output as JSON
        let constraints_json: Vec<serde_json::Value> = constraints
            .iter()
            .map(|c| {
                serde_json::json!({
                    "kind": c.kind.as_str(),
                    "name": c.name,
                    "type": c.type_info,
                    "location": c.location,
                })
            })
            .collect();

        let output = serde_json::json!({
            "file": path.display().to_string(),
            "items": ast.items.len(),
            "constraints": constraints.len(),
            "data": constraints_json,
        });

        println!("{}", serde_json::to_string_pretty(&output).unwrap());
    } else {
        // Text output
        println!("Constraint Analysis: {}", path.display());
        println!("  Items: {}", ast.items.len());
        println!("  Type constraints: {}", constraints.len());
        println!();

        if verbose {
            // Group by kind
            let mut by_kind: std::collections::HashMap<&str, Vec<&TypeConstraint>> = std::collections::HashMap::new();
            for c in &constraints {
                by_kind.entry(c.kind.as_str()).or_default().push(c);
            }

            for (kind, items) in &by_kind {
                println!("{}:", kind);
                for c in items {
                    println!("  {} : {} ({})", c.name, c.type_info, c.location);
                }
                println!();
            }
        } else {
            // Summary only
            let func_count = constraints
                .iter()
                .filter(|c| matches!(c.kind, ConstraintKind::FunctionSignature))
                .count();
            let field_count = constraints
                .iter()
                .filter(|c| matches!(c.kind, ConstraintKind::FieldType))
                .count();
            let var_count = constraints
                .iter()
                .filter(|c| matches!(c.kind, ConstraintKind::VariableDecl))
                .count();
            let bound_count = constraints
                .iter()
                .filter(|c| matches!(c.kind, ConstraintKind::TraitBound))
                .count();

            println!("  Function signatures: {}", func_count);
            println!("  Field types: {}", field_count);
            println!("  Variable declarations: {}", var_count);
            println!("  Trait bounds: {}", bound_count);
            println!();
            println!("Use --verbose to see all constraints.");
        }
    }

    0
}
