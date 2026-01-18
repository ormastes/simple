//! LSP MCP Module
//!
//! Exposes Language Server Protocol functionality via MCP (Model Context Protocol).
//! This module provides LSP-like code intelligence tools that can be called via MCP.
//!
//! ## Available Tools
//!
//! - `lsp_definition` - Find where a symbol is defined
//! - `lsp_references` - Find all references to a symbol
//! - `lsp_hover` - Get type info and documentation
//! - `lsp_symbols` - List all symbols in a file
//! - `lsp_diagnostics` - Get parse and semantic errors
//!
//! ## Usage
//!
//! ```rust,ignore
//! use simple_compiler::lsp_mcp::{LspMcpTools, Position, SymbolInfo};
//!
//! let mut tools = LspMcpTools::new();
//!
//! // Get all symbols in a file
//! let symbols = tools.document_symbols("file.spl", source);
//!
//! // Go to definition
//! let location = tools.go_to_definition("file.spl", source, 5, 10);
//!
//! // Get hover info
//! let hover = tools.hover("file.spl", source, 5, 10);
//! ```
//!
//! ## JSON-RPC Tool Format
//!
//! When used via MCP, the tools accept JSON input and produce JSON output:
//!
//! ```json
//! // lsp_symbols request
//! {"file": "path.spl"}
//!
//! // lsp_definition request
//! {"file": "path.spl", "line": 5, "character": 10}
//!
//! // lsp_references request
//! {"file": "path.spl", "line": 1, "character": 5, "include_declaration": true}
//! ```

pub mod tools;
pub mod types;

// Re-export main types
pub use tools::LspMcpTools;
pub use types::{
    Diagnostic, DiagnosticSeverity, HoverContents, HoverInfo, Location, Position, Range, ReferenceContext,
    ReferenceLocation, SymbolInfo, SymbolKind,
};

use serde::{Deserialize, Serialize};
use serde_json::Value;

/// Input parameters for lsp_definition tool
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefinitionParams {
    /// File path
    pub file: String,
    /// Line number (0-based)
    pub line: u32,
    /// Character offset (0-based)
    pub character: u32,
}

/// Input parameters for lsp_references tool
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReferencesParams {
    /// File path
    pub file: String,
    /// Line number (0-based)
    pub line: u32,
    /// Character offset (0-based)
    pub character: u32,
    /// Include the declaration in results
    #[serde(default = "default_true")]
    pub include_declaration: bool,
}

fn default_true() -> bool {
    true
}

/// Input parameters for lsp_hover tool
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HoverParams {
    /// File path
    pub file: String,
    /// Line number (0-based)
    pub line: u32,
    /// Character offset (0-based)
    pub character: u32,
}

/// Input parameters for lsp_symbols tool
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SymbolsParams {
    /// File path
    pub file: String,
}

/// Input parameters for lsp_diagnostics tool
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiagnosticsParams {
    /// File path
    pub file: String,
    /// Include warnings (not just errors)
    #[serde(default)]
    pub include_warnings: bool,
}

/// MCP Tool handler for LSP operations
pub struct LspMcpHandler {
    tools: LspMcpTools,
}

impl Default for LspMcpHandler {
    fn default() -> Self {
        Self::new()
    }
}

impl LspMcpHandler {
    /// Create a new LSP MCP handler
    pub fn new() -> Self {
        Self {
            tools: LspMcpTools::new(),
        }
    }

    /// Handle lsp_definition tool call
    pub fn handle_definition(&mut self, params: DefinitionParams, source: &str) -> Value {
        match self.tools.go_to_definition(&params.file, source, params.line, params.character) {
            Some(location) => serde_json::to_value(&location).unwrap_or(Value::Null),
            None => Value::Null,
        }
    }

    /// Handle lsp_references tool call
    pub fn handle_references(&mut self, params: ReferencesParams, source: &str) -> Value {
        let refs = self.tools.find_references(
            &params.file,
            source,
            params.line,
            params.character,
            params.include_declaration,
        );
        serde_json::to_value(&refs).unwrap_or(Value::Array(vec![]))
    }

    /// Handle lsp_hover tool call
    pub fn handle_hover(&mut self, params: HoverParams, source: &str) -> Value {
        match self.tools.hover(&params.file, source, params.line, params.character) {
            Some(hover) => serde_json::to_value(&hover).unwrap_or(Value::Null),
            None => Value::Null,
        }
    }

    /// Handle lsp_symbols tool call
    pub fn handle_symbols(&mut self, params: SymbolsParams, source: &str) -> Value {
        let symbols = self.tools.document_symbols(&params.file, source);
        serde_json::to_value(&symbols).unwrap_or(Value::Array(vec![]))
    }

    /// Handle lsp_diagnostics tool call
    pub fn handle_diagnostics(&mut self, params: DiagnosticsParams, source: &str) -> Value {
        let diagnostics = self.tools.diagnostics(&params.file, source, params.include_warnings);
        serde_json::to_value(&diagnostics).unwrap_or(Value::Array(vec![]))
    }

    /// Generic tool call dispatcher
    pub fn call_tool(&mut self, tool_name: &str, args: Value, source: &str) -> Result<Value, String> {
        match tool_name {
            "lsp_definition" => {
                let params: DefinitionParams =
                    serde_json::from_value(args).map_err(|e| format!("Invalid params: {}", e))?;
                Ok(self.handle_definition(params, source))
            }
            "lsp_references" => {
                let params: ReferencesParams =
                    serde_json::from_value(args).map_err(|e| format!("Invalid params: {}", e))?;
                Ok(self.handle_references(params, source))
            }
            "lsp_hover" => {
                let params: HoverParams = serde_json::from_value(args).map_err(|e| format!("Invalid params: {}", e))?;
                Ok(self.handle_hover(params, source))
            }
            "lsp_symbols" => {
                let params: SymbolsParams =
                    serde_json::from_value(args).map_err(|e| format!("Invalid params: {}", e))?;
                Ok(self.handle_symbols(params, source))
            }
            "lsp_diagnostics" => {
                let params: DiagnosticsParams =
                    serde_json::from_value(args).map_err(|e| format!("Invalid params: {}", e))?;
                Ok(self.handle_diagnostics(params, source))
            }
            _ => Err(format!("Unknown tool: {}", tool_name)),
        }
    }
}

/// Get tool definitions for MCP registration
pub fn get_tool_definitions() -> Vec<Value> {
    vec![
        serde_json::json!({
            "name": "lsp_definition",
            "description": "Find the definition location of a symbol at a given position",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "file": {"type": "string", "description": "File path"},
                    "line": {"type": "integer", "description": "Line number (0-based)"},
                    "character": {"type": "integer", "description": "Character offset (0-based)"}
                },
                "required": ["file", "line", "character"]
            }
        }),
        serde_json::json!({
            "name": "lsp_references",
            "description": "Find all references to a symbol at a given position",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "file": {"type": "string", "description": "File path"},
                    "line": {"type": "integer", "description": "Line number (0-based)"},
                    "character": {"type": "integer", "description": "Character offset (0-based)"},
                    "include_declaration": {"type": "boolean", "description": "Include the declaration in results", "default": true}
                },
                "required": ["file", "line", "character"]
            }
        }),
        serde_json::json!({
            "name": "lsp_hover",
            "description": "Get hover information (type info, documentation) for a symbol",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "file": {"type": "string", "description": "File path"},
                    "line": {"type": "integer", "description": "Line number (0-based)"},
                    "character": {"type": "integer", "description": "Character offset (0-based)"}
                },
                "required": ["file", "line", "character"]
            }
        }),
        serde_json::json!({
            "name": "lsp_symbols",
            "description": "Get all symbols (functions, classes, variables) in a document",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "file": {"type": "string", "description": "File path"}
                },
                "required": ["file"]
            }
        }),
        serde_json::json!({
            "name": "lsp_diagnostics",
            "description": "Get parse errors and semantic warnings for a file",
            "inputSchema": {
                "type": "object",
                "properties": {
                    "file": {"type": "string", "description": "File path"},
                    "include_warnings": {"type": "boolean", "description": "Include warnings (not just errors)", "default": false}
                },
                "required": ["file"]
            }
        }),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_handler_symbols() {
        let mut handler = LspMcpHandler::new();
        let source = r#"
pub fn test():
    pass
"#;
        let params = SymbolsParams {
            file: "test.spl".to_string(),
        };

        let result = handler.handle_symbols(params, source);
        assert!(result.is_array());
    }

    #[test]
    fn test_handler_diagnostics() {
        let mut handler = LspMcpHandler::new();
        let source = r#"
fn valid():
    pass
"#;
        let params = DiagnosticsParams {
            file: "test.spl".to_string(),
            include_warnings: false,
        };

        let result = handler.handle_diagnostics(params, source);
        assert!(result.is_array());
        assert!(result.as_array().unwrap().is_empty());
    }

    #[test]
    fn test_tool_definitions() {
        let defs = get_tool_definitions();
        assert_eq!(defs.len(), 5);

        let names: Vec<_> = defs.iter().map(|d| d["name"].as_str().unwrap()).collect();
        assert!(names.contains(&"lsp_definition"));
        assert!(names.contains(&"lsp_references"));
        assert!(names.contains(&"lsp_hover"));
        assert!(names.contains(&"lsp_symbols"));
        assert!(names.contains(&"lsp_diagnostics"));
    }

    #[test]
    fn test_call_tool() {
        let mut handler = LspMcpHandler::new();
        let source = "fn test(): pass";

        let args = serde_json::json!({
            "file": "test.spl"
        });

        let result = handler.call_tool("lsp_symbols", args, source);
        assert!(result.is_ok());
    }
}
