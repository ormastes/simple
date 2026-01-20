//! FFI Bridge for Parser and API Surface
//!
//! Exposes compiler functionality (Parser, ApiSurface) to Simple code via FFI.
//! This allows Simple stdlib to parse and analyze Simple source code.

use simple_parser::{Parser, ParserMode};
use simple_runtime::value::core::RuntimeValue;
use simple_runtime::value::rt_string_from_str;
use crate::api_surface::ApiSurface;
use std::path::Path;

/// Parse a Simple source file and return the AST as JSON
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
    let mut parser = Parser::new(&content, ParserMode::Standard);
    let module = match parser.parse_module() {
        Ok(m) => m,
        Err(_) => return RuntimeValue::NIL,
    };

    // Convert AST to JSON string
    let json = match serde_json::to_string_pretty(&module) {
        Ok(j) => j,
        Err(_) => return RuntimeValue::NIL,
    };

    rt_string_from_str(&json)
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
    let mut parser = Parser::new(&content, ParserMode::Standard);
    let module = match parser.parse_module() {
        Ok(m) => m,
        Err(_) => return RuntimeValue::NIL,
    };

    // Extract API surface
    let api_surface = ApiSurface::from_module(&module, Path::new(&path_str).file_stem().unwrap_or_default().to_string_lossy().to_string());

    // Convert to JSON
    let json = match serde_json::to_string_pretty(&api_surface) {
        Ok(j) => j,
        Err(_) => return RuntimeValue::NIL,
    };

    rt_string_from_str(&json)
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
    let mut parser = Parser::new(&content, ParserMode::Standard);
    let module = match parser.parse_module() {
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

    rt_string_from_str(&json)
}

// Helper: Convert RuntimeValue to Rust String
fn runtime_value_to_string(val: RuntimeValue) -> Option<String> {
    if !val.is_heap() {
        return None;
    }

    unsafe {
        let ptr = val.as_heap_ptr();
        use simple_runtime::value::heap::{HeapHeader, HeapObjectType};
        if (*ptr).object_type != HeapObjectType::String {
            return None;
        }

        use simple_runtime::value::collections::RuntimeString;
        let str_ptr = ptr as *const RuntimeString;
        let len = (*str_ptr).len as usize;
        let data_ptr = (str_ptr as *const u8).add(std::mem::size_of::<RuntimeString>());
        let bytes = std::slice::from_raw_parts(data_ptr, len);
        String::from_utf8(bytes.to_vec()).ok()
    }
}

// Helper: Find all symbols used by a function
fn find_used_symbols(module: &simple_parser::ast::Module, target: &str) -> Vec<String> {
    use simple_parser::ast::Node;
    let mut symbols = Vec::new();

    // Find the target function
    for item in &module.items {
        if let Node::FunctionDef(func) = item {
            if func.name == target {
                // Walk the function body to collect all symbol references
                collect_symbols_from_node(&func.body, &mut symbols);
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
fn collect_symbols_from_node(node: &Node, symbols: &mut Vec<String>) {
    use simple_parser::ast::Node;

    match node {
        Node::Identifier(name) => {
            symbols.push(name.clone());
        }
        Node::Call(call) => {
            collect_symbols_from_node(&call.callee, symbols);
            for arg in &call.arguments {
                collect_symbols_from_node(arg, symbols);
            }
        }
        Node::BinaryOp(bin) => {
            collect_symbols_from_node(&bin.left, symbols);
            collect_symbols_from_node(&bin.right, symbols);
        }
        Node::Block(block) => {
            for stmt in &block.statements {
                collect_symbols_from_node(stmt, symbols);
            }
        }
        Node::IfStmt(if_stmt) => {
            collect_symbols_from_node(&if_stmt.condition, symbols);
            collect_symbols_from_node(&if_stmt.then_block, symbols);
            if let Some(else_block) = &if_stmt.else_block {
                collect_symbols_from_node(else_block, symbols);
            }
        }
        Node::Return(ret) => {
            if let Some(value) = &ret.value {
                collect_symbols_from_node(value, symbols);
            }
        }
        Node::Assignment(assign) => {
            collect_symbols_from_node(&assign.value, symbols);
        }
        Node::MethodCall(method) => {
            collect_symbols_from_node(&method.receiver, symbols);
            for arg in &method.arguments {
                collect_symbols_from_node(arg, symbols);
            }
        }
        // Add more node types as needed
        _ => {}
    }
}
