//! LSP-MCP module.
//!
//! This module exposes Language Server Protocol functionality via MCP tools,
//! enabling LLM-friendly code intelligence features.

mod tools;
mod types;

pub use tools::{file_uri, LspMcpTools};
pub use types::*;

use serde::{Deserialize, Serialize};

/// Parameters for the lsp_definition tool
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DefinitionParams {
    /// File path
    pub file: String,
    /// Line number (0-indexed)
    pub line: u32,
    /// Character offset (0-indexed)
    pub character: u32,
}

/// Parameters for the lsp_references tool
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReferencesParams {
    /// File path
    pub file: String,
    /// Line number (0-indexed)
    pub line: u32,
    /// Character offset (0-indexed)
    pub character: u32,
    /// Whether to include the declaration
    #[serde(default = "default_true")]
    pub include_declaration: bool,
}

fn default_true() -> bool {
    true
}

/// Parameters for the lsp_hover tool
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HoverParams {
    /// File path
    pub file: String,
    /// Line number (0-indexed)
    pub line: u32,
    /// Character offset (0-indexed)
    pub character: u32,
}

/// Parameters for the lsp_symbols tool
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SymbolsParams {
    /// File path
    pub file: String,
}

/// Parameters for the lsp_diagnostics tool
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiagnosticsParams {
    /// File path
    pub file: String,
    /// Whether to include warnings (default: true)
    #[serde(default = "default_true")]
    pub include_warnings: bool,
}

/// Tool definition for MCP registration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ToolDefinition {
    /// Tool name
    pub name: String,
    /// Tool description
    pub description: String,
    /// Input schema (JSON Schema)
    pub input_schema: serde_json::Value,
}

/// Get all LSP-MCP tool definitions
pub fn get_tool_definitions() -> Vec<ToolDefinition> {
    vec![
        ToolDefinition {
            name: "lsp_definition".to_string(),
            description: "Find where a symbol is defined. Returns the location of the symbol's definition."
                .to_string(),
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "file": {
                        "type": "string",
                        "description": "Path to the source file"
                    },
                    "line": {
                        "type": "integer",
                        "description": "Line number (0-indexed)"
                    },
                    "character": {
                        "type": "integer",
                        "description": "Character offset (0-indexed)"
                    }
                },
                "required": ["file", "line", "character"]
            }),
        },
        ToolDefinition {
            name: "lsp_references".to_string(),
            description: "Find all references to a symbol. Returns all locations where the symbol is used."
                .to_string(),
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "file": {
                        "type": "string",
                        "description": "Path to the source file"
                    },
                    "line": {
                        "type": "integer",
                        "description": "Line number (0-indexed)"
                    },
                    "character": {
                        "type": "integer",
                        "description": "Character offset (0-indexed)"
                    },
                    "include_declaration": {
                        "type": "boolean",
                        "description": "Include the declaration in results (default: true)"
                    }
                },
                "required": ["file", "line", "character"]
            }),
        },
        ToolDefinition {
            name: "lsp_hover".to_string(),
            description: "Get hover information for a symbol. Returns type information and documentation."
                .to_string(),
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "file": {
                        "type": "string",
                        "description": "Path to the source file"
                    },
                    "line": {
                        "type": "integer",
                        "description": "Line number (0-indexed)"
                    },
                    "character": {
                        "type": "integer",
                        "description": "Character offset (0-indexed)"
                    }
                },
                "required": ["file", "line", "character"]
            }),
        },
        ToolDefinition {
            name: "lsp_symbols".to_string(),
            description: "List all symbols in a file. Returns functions, classes, structs, enums, etc.".to_string(),
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "file": {
                        "type": "string",
                        "description": "Path to the source file"
                    }
                },
                "required": ["file"]
            }),
        },
        ToolDefinition {
            name: "lsp_diagnostics".to_string(),
            description: "Get diagnostics for a file. Returns parse errors, type errors, and lint warnings."
                .to_string(),
            input_schema: serde_json::json!({
                "type": "object",
                "properties": {
                    "file": {
                        "type": "string",
                        "description": "Path to the source file"
                    },
                    "include_warnings": {
                        "type": "boolean",
                        "description": "Include lint warnings (default: true)"
                    }
                },
                "required": ["file"]
            }),
        },
    ]
}

/// Handler for LSP-MCP tools
pub struct LspMcpHandler {
    tools: LspMcpTools,
}

impl Default for LspMcpHandler {
    fn default() -> Self {
        Self::new()
    }
}

impl LspMcpHandler {
    /// Create a new handler
    pub fn new() -> Self {
        Self {
            tools: LspMcpTools::new(),
        }
    }

    /// Handle lsp_definition tool call (requires source to be passed)
    pub fn handle_definition_with_source(
        &mut self,
        params: DefinitionParams,
        source: &str,
    ) -> Result<Option<Location>, String> {
        Ok(self.tools.go_to_definition(&params.file, source, params.line, params.character))
    }

    /// Handle lsp_references tool call (requires source to be passed)
    pub fn handle_references_with_source(
        &mut self,
        params: ReferencesParams,
        source: &str,
    ) -> Result<Vec<ReferenceLocation>, String> {
        Ok(self.tools.find_references(
            &params.file,
            source,
            params.line,
            params.character,
            params.include_declaration,
        ))
    }

    /// Handle lsp_hover tool call (requires source to be passed)
    pub fn handle_hover_with_source(
        &mut self,
        params: HoverParams,
        source: &str,
    ) -> Result<Option<HoverInfo>, String> {
        Ok(self.tools.hover(&params.file, source, params.line, params.character))
    }

    /// Handle lsp_symbols tool call (requires source to be passed)
    pub fn handle_symbols_with_source(
        &mut self,
        params: SymbolsParams,
        source: &str,
    ) -> Result<Vec<SymbolInfo>, String> {
        Ok(self.tools.document_symbols(&params.file, source))
    }

    /// Handle lsp_diagnostics tool call (requires source to be passed)
    pub fn handle_diagnostics_with_source(
        &mut self,
        params: DiagnosticsParams,
        source: &str,
    ) -> Result<Vec<Diagnostic>, String> {
        Ok(self.tools.diagnostics(&params.file, source, params.include_warnings))
    }

    /// Invalidate the cache for a file
    pub fn invalidate(&mut self, path: &str) {
        self.tools.invalidate(path);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_tool_definitions() {
        let tools = get_tool_definitions();
        assert_eq!(tools.len(), 5);
        assert!(tools.iter().any(|t| t.name == "lsp_definition"));
        assert!(tools.iter().any(|t| t.name == "lsp_references"));
        assert!(tools.iter().any(|t| t.name == "lsp_hover"));
        assert!(tools.iter().any(|t| t.name == "lsp_symbols"));
        assert!(tools.iter().any(|t| t.name == "lsp_diagnostics"));
    }

    #[test]
    fn test_definition_params_deserialize() {
        let json = r#"{"file": "test.spl", "line": 5, "character": 10}"#;
        let params: DefinitionParams = serde_json::from_str(json).unwrap();
        assert_eq!(params.file, "test.spl");
        assert_eq!(params.line, 5);
        assert_eq!(params.character, 10);
    }

    #[test]
    fn test_references_params_default() {
        let json = r#"{"file": "test.spl", "line": 5, "character": 10}"#;
        let params: ReferencesParams = serde_json::from_str(json).unwrap();
        assert!(params.include_declaration);
    }
}
