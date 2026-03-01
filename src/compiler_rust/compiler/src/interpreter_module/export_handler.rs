//! Export handling for the Simple interpreter.
//!
//! This module handles loading modules for re-export statements
//! (e.g., `export X, Y from module`).

use std::collections::HashMap;
use std::path::Path;

use tracing::{instrument, trace, warn};

use simple_parser::ast::{ClassDef, EnumDef, ExportUseStmt, ImportTarget, UseStmt};

use crate::error::CompileError;
use crate::value::Value;

use super::module_loader::load_and_merge_module;

type Enums = HashMap<String, EnumDef>;

/// Load a module for re-export (export X from Y)
#[instrument(skip(export_stmt, current_file, functions, classes, enums), fields(path = ?export_stmt.path.segments))]
pub fn load_export_source(
    export_stmt: &ExportUseStmt,
    current_file: Option<&Path>,
    functions: &mut HashMap<String, simple_parser::ast::FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &mut Enums,
) -> Result<HashMap<String, Value>, CompileError> {
    trace!(path = ?export_stmt.path.segments, target = ?export_stmt.target, "Loading export source");

    // Skip if path is empty - this happens with bare exports like `export X`
    // which mark local symbols for export, not re-exports from other modules
    if export_stmt.path.segments.is_empty() {
        trace!("Skipping export with empty path (bare export)");
        return Ok(HashMap::new());
    }

    // Build a UseStmt to load the source module
    let use_stmt = UseStmt {
        span: export_stmt.span.clone(),
        path: export_stmt.path.clone(),
        target: ImportTarget::Glob, // Load entire module to get all exports
        is_type_only: false,        // Runtime export loading is never type-only
        is_lazy: false,
    };

    match load_and_merge_module(&use_stmt, current_file, functions, classes, enums) {
        Ok(Value::Dict(dict)) => Ok(dict),
        Ok(_) => Ok(HashMap::new()),
        Err(e) => {
            warn!(error = %e, "Failed to load export source");
            Ok(HashMap::new())
        }
    }
}
