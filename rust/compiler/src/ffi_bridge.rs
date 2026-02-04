//! FFI Bridge for Parser and API Surface
//!
//! Exposes compiler functionality (Parser, ApiSurface) to Simple code via FFI.
//! This allows Simple stdlib to parse and analyze Simple source code.

use simple_parser::Parser;
use simple_runtime::value::{RuntimeValue, rt_string_new, HeapHeader, HeapObjectType, RuntimeString};
use crate::api_surface::ApiSurface;
use std::path::Path;

/// Parse a Simple source file and return the AST as a debug string
#[no_mangle]
pub extern "C" fn rt_parse_simple_file(path: RuntimeValue) -> RuntimeValue {
    // Convert RuntimeValue to string path
    let path_str = match runtime_value_to_string(path) {
        Some(s) => s,
        None => return RuntimeValue::NIL,
    };

    // Read file content
    let content = match std::fs::read_to_string(&path_str) {
        Ok(c) => c,
        Err(_) => return RuntimeValue::NIL,
    };

    // Parse with Parser
    let mut parser = Parser::new(&content);
    let module = match parser.parse() {
        Ok(m) => m,
        Err(_) => return RuntimeValue::NIL,
    };

    // Convert AST to debug string (since Module doesn't impl Serialize)
    let debug_str = format!("{:#?}", module);
    string_to_runtime_value(&debug_str)
}

/// Extract API surface from a Simple source file
#[no_mangle]
pub extern "C" fn rt_api_surface_extract(path: RuntimeValue) -> RuntimeValue {
    // Convert RuntimeValue to string path
    let path_str = match runtime_value_to_string(path) {
        Some(s) => s,
        None => return RuntimeValue::NIL,
    };

    // Read file content
    let content = match std::fs::read_to_string(&path_str) {
        Ok(c) => c,
        Err(_) => return RuntimeValue::NIL,
    };

    // Parse with Parser
    let mut parser = Parser::new(&content);
    let module = match parser.parse() {
        Ok(m) => m,
        Err(_) => return RuntimeValue::NIL,
    };

    // Extract API surface from parsed nodes
    let module_name = Path::new(&path_str)
        .file_stem()
        .unwrap_or_default()
        .to_string_lossy()
        .to_string();
    let api_surface = ApiSurface::from_nodes(module_name, &module.items);

    // Convert to JSON
    let json = match serde_json::to_string_pretty(&api_surface) {
        Ok(j) => j,
        Err(_) => return RuntimeValue::NIL,
    };

    string_to_runtime_value(&json)
}

/// Find all symbols used by a target function in a Simple source file
#[no_mangle]
pub extern "C" fn rt_symbol_usage_find(path: RuntimeValue, target: RuntimeValue) -> RuntimeValue {
    // Convert RuntimeValue to strings
    let path_str = match runtime_value_to_string(path) {
        Some(s) => s,
        None => return RuntimeValue::NIL,
    };
    let target_str = match runtime_value_to_string(target) {
        Some(s) => s,
        None => return RuntimeValue::NIL,
    };

    // Read file content
    let content = match std::fs::read_to_string(&path_str) {
        Ok(c) => c,
        Err(_) => return RuntimeValue::NIL,
    };

    // Parse with Parser
    let mut parser = Parser::new(&content);
    let module = match parser.parse() {
        Ok(m) => m,
        Err(_) => return RuntimeValue::NIL,
    };

    // Find symbols used by target function
    let symbols = find_used_symbols(&module, &target_str);

    // Convert to JSON array
    let json = match serde_json::to_string(&symbols) {
        Ok(j) => j,
        Err(_) => return RuntimeValue::NIL,
    };

    string_to_runtime_value(&json)
}

// Helper: Convert RuntimeValue to Rust String
fn runtime_value_to_string(val: RuntimeValue) -> Option<String> {
    if !val.is_heap() {
        return None;
    }

    unsafe {
        let ptr = val.as_heap_ptr();
        if (*ptr).object_type != HeapObjectType::String {
            return None;
        }

        let str_ptr = ptr as *const RuntimeString;
        let len = (*str_ptr).len as usize;
        let data_ptr = (str_ptr as *const u8).add(std::mem::size_of::<RuntimeString>());
        let bytes = std::slice::from_raw_parts(data_ptr, len);
        String::from_utf8(bytes.to_vec()).ok()
    }
}

// Helper: Convert Rust String to RuntimeValue
fn string_to_runtime_value(s: &str) -> RuntimeValue {
    rt_string_new(s.as_ptr(), s.len() as u64)
}

// Helper: Find all symbols used by a function
fn find_used_symbols(module: &simple_parser::ast::Module, target: &str) -> Vec<String> {
    use simple_parser::Node;
    let mut symbols = Vec::new();

    // Find the target function
    for item in &module.items {
        if let Node::Function(func) = item {
            if func.name == target {
                // Walk the function body to collect all symbol references
                for stmt in &func.body.statements {
                    collect_symbols_from_node(stmt, &mut symbols);
                }
                break;
            }
        }
    }

    // Deduplicate
    symbols.sort();
    symbols.dedup();
    symbols
}

// Helper: Recursively collect symbol references from AST node
fn collect_symbols_from_node(node: &simple_parser::Node, symbols: &mut Vec<String>) {
    use simple_parser::Node;

    match node {
        Node::Expression(expr) => {
            collect_symbols_from_expr(expr, symbols);
        }
        Node::Return(ret) => {
            if let Some(value) = &ret.value {
                collect_symbols_from_expr(value, symbols);
            }
        }
        Node::Assignment(assign) => {
            collect_symbols_from_expr(&assign.target, symbols);
            collect_symbols_from_expr(&assign.value, symbols);
        }
        Node::If(if_stmt) => {
            collect_symbols_from_expr(&if_stmt.condition, symbols);
            for stmt in &if_stmt.then_block.statements {
                collect_symbols_from_node(stmt, symbols);
            }
            if let Some(else_block) = &if_stmt.else_block {
                for stmt in &else_block.statements {
                    collect_symbols_from_node(stmt, symbols);
                }
            }
        }
        Node::While(while_stmt) => {
            collect_symbols_from_expr(&while_stmt.condition, symbols);
            for stmt in &while_stmt.body.statements {
                collect_symbols_from_node(stmt, symbols);
            }
        }
        Node::Let(let_stmt) => {
            if let Some(value) = &let_stmt.value {
                collect_symbols_from_expr(value, symbols);
            }
        }
        // Add more node types as needed
        _ => {}
    }
}

// Helper: Collect symbols from expressions
fn collect_symbols_from_expr(expr: &simple_parser::Expr, symbols: &mut Vec<String>) {
    use simple_parser::Expr;

    match expr {
        Expr::Identifier(name) => {
            symbols.push(name.clone());
        }
        Expr::Call { callee, args, .. } => {
            collect_symbols_from_expr(callee, symbols);
            for arg in args {
                collect_symbols_from_expr(&arg.value, symbols);
            }
        }
        Expr::Binary { left, right, .. } => {
            collect_symbols_from_expr(left, symbols);
            collect_symbols_from_expr(right, symbols);
        }
        Expr::MethodCall { receiver, args, .. } => {
            collect_symbols_from_expr(receiver, symbols);
            for arg in args {
                collect_symbols_from_expr(&arg.value, symbols);
            }
        }
        Expr::FieldAccess { receiver, .. } => {
            collect_symbols_from_expr(receiver, symbols);
        }
        Expr::Index { receiver, index } => {
            collect_symbols_from_expr(receiver, symbols);
            collect_symbols_from_expr(index, symbols);
        }
        // Add more expression types as needed
        _ => {}
    }
}
