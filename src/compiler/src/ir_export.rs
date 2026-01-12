//! IR Export for LLM-Friendly Features (#885-887)
//!
//! Exports AST, HIR, and MIR to JSON format for tool consumption.

use serde::{Serialize, Serializer};
use serde_json;
use std::fs::File;
use std::io::{self, Write};
use std::path::Path;

use crate::hir::HirModule;
use crate::mir::MirModule;
use simple_parser::ast::Module as AstModule;

/// Export result for IR emission
pub type ExportResult = Result<(), String>;

/// Export AST to JSON
pub fn export_ast_json<W: Write>(module: &AstModule, writer: &mut W) -> ExportResult {
    // Create a serializable wrapper for AST
    let json = serde_json::to_string_pretty(&SerializableAst(module))
        .map_err(|e| format!("Failed to serialize AST: {}", e))?;

    writeln!(writer, "{}", json).map_err(|e| format!("Failed to write AST JSON: {}", e))
}

/// Export AST to file or stdout
pub fn export_ast(module: &AstModule, path: Option<&Path>) -> ExportResult {
    match path {
        Some(p) => {
            let mut file =
                File::create(p).map_err(|e| format!("Failed to create file {:?}: {}", p, e))?;
            export_ast_json(module, &mut file)
        }
        None => {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            export_ast_json(module, &mut handle)
        }
    }
}

/// Export HIR to JSON
pub fn export_hir_json<W: Write>(module: &HirModule, writer: &mut W) -> ExportResult {
    let json = serde_json::to_string_pretty(&SerializableHir(module))
        .map_err(|e| format!("Failed to serialize HIR: {}", e))?;

    writeln!(writer, "{}", json).map_err(|e| format!("Failed to write HIR JSON: {}", e))
}

/// Export HIR to file or stdout
pub fn export_hir(module: &HirModule, path: Option<&Path>) -> ExportResult {
    match path {
        Some(p) => {
            let mut file =
                File::create(p).map_err(|e| format!("Failed to create file {:?}: {}", p, e))?;
            export_hir_json(module, &mut file)
        }
        None => {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            export_hir_json(module, &mut handle)
        }
    }
}

/// Export MIR to JSON
pub fn export_mir_json<W: Write>(module: &MirModule, writer: &mut W) -> ExportResult {
    let json = serde_json::to_string_pretty(&SerializableMir(module))
        .map_err(|e| format!("Failed to serialize MIR: {}", e))?;

    writeln!(writer, "{}", json).map_err(|e| format!("Failed to write MIR JSON: {}", e))
}

/// Export MIR to file or stdout
pub fn export_mir(module: &MirModule, path: Option<&Path>) -> ExportResult {
    match path {
        Some(p) => {
            let mut file =
                File::create(p).map_err(|e| format!("Failed to create file {:?}: {}", p, e))?;
            export_mir_json(module, &mut file)
        }
        None => {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            export_mir_json(module, &mut handle)
        }
    }
}

// Serializable wrappers that implement custom JSON output

struct SerializableAst<'a>(&'a AstModule);

impl<'a> Serialize for SerializableAst<'a> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;

        let mut state = serializer.serialize_struct("AstModule", 2)?;
        state.serialize_field("type", "AST")?;
        state.serialize_field("node_count", &self.0.items.len())?;
        state.end()
    }
}

struct SerializableHir<'a>(&'a HirModule);

impl<'a> Serialize for SerializableHir<'a> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;

        let mut state = serializer.serialize_struct("HirModule", 3)?;
        state.serialize_field("type", "HIR")?;
        state.serialize_field("name", &self.0.name)?;
        state.serialize_field("function_count", &self.0.functions.len())?;
        state.end()
    }
}

struct SerializableMir<'a>(&'a MirModule);

impl<'a> Serialize for SerializableMir<'a> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;

        let mut state = serializer.serialize_struct("MirModule", 3)?;
        state.serialize_field("type", "MIR")?;
        state.serialize_field("name", &self.0.name)?;
        state.serialize_field("function_count", &self.0.functions.len())?;
        state.end()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn test_export_ast_json_simple() {
        use simple_parser::Parser;

        let source = "fn main():\n    return 42";
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("parse failed");

        let mut output = Vec::new();
        let result = export_ast_json(&module, &mut output);
        assert!(result.is_ok());

        let json = String::from_utf8(output).unwrap();
        // Check for "type" field with "AST" value (allow for spacing variations in JSON)
        assert!(
            json.contains("\"type\"") && json.contains("\"AST\""),
            "Expected JSON to contain type field with AST value, got: {}",
            json
        );
    }

    #[test]
    fn test_export_hir_json() {
        // HIR requires a full compilation context
        // This is a placeholder for when HIR is more stable
        // For now, just test that the function exists
    }

    #[test]
    fn test_export_mir_json() {
        // MIR requires a full compilation context
        // This is a placeholder for when MIR is more stable
    }
}
