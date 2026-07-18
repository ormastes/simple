//! Export handling for the Simple interpreter.
//!
//! This module handles loading modules for re-export statements
//! (e.g., `export X, Y from module`).

use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;

use tracing::{instrument, trace, warn};

use simple_parser::ast::{ClassDef, EnumDef, ExportUseStmt, ImportTarget, UseStmt};

use crate::error::CompileError;
use crate::value::Value;

use super::module_loader::load_and_merge_module;

type Enums = HashMap<String, Arc<EnumDef>>;

/// Load a module for re-export (export X from Y)
#[instrument(skip(export_stmt, current_file, functions, classes, enums), fields(path = ?export_stmt.path.segments))]
pub fn load_export_source(
    export_stmt: &ExportUseStmt,
    current_file: Option<&Path>,
    functions: &mut HashMap<String, Arc<simple_parser::ast::FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &mut Enums,
) -> Result<HashMap<String, Value>, CompileError> {
    trace!(path = ?export_stmt.path.segments, target = ?export_stmt.target, "Loading export source");

    // Skip if path is empty - this happens with bare exports like `export X`
    // which mark local symbols for export, not re-exports from other modules
    if export_stmt.path.segments.is_empty() {
        trace!("Skipping export with empty path (bare export)");
        return Ok(HashMap::new());
    }

    // Build a UseStmt to load the source module. This always loads the full
    // module regardless of target (see the `requested_names`/"Keep the full
    // module" comment in `load_and_merge_module`) — callers here re-filter
    // the returned dict by `export_stmt.target` themselves. But the target
    // ALSO feeds the file-vs-same-named-package precedence decision
    // (`prefer_package_init_for_member_import`), which needs the real
    // requested names to avoid redirecting a `Group` re-export away from a
    // sibling FILE that defines them into a same-named PACKAGE that doesn't
    // (see
    // doc/08_tracking/bug/std_spec_package_shadows_file_print_summary_2026-07-17.md:
    // `export use std.nogc_sync_mut.spec.{.., print_summary, ..}` was
    // hardcoding `Glob` here, discarding the specific names before that
    // precedence check ever saw them). Preserve `Group` targets so that
    // check works; keep every other target forced to `Glob` exactly as
    // before (`Single`/`Aliased` in particular must stay `Glob` — those
    // extract a single value rather than a `Dict`, which would break the
    // `Ok(Value::Dict(dict))` match below).
    let use_target = match &export_stmt.target {
        ImportTarget::Group(_) => export_stmt.target.clone(),
        _ => ImportTarget::Glob,
    };
    let use_stmt = UseStmt {
        span: export_stmt.span,
        path: export_stmt.path.clone(),
        target: use_target,
        is_type_only: false, // Runtime export loading is never type-only
        is_lazy: false,
    };

    match load_and_merge_module(&use_stmt, current_file, functions, classes, enums) {
        Ok(Value::Dict(dict)) => Ok(HashMap::clone(&dict)),
        Ok(_) => Ok(HashMap::new()),
        Err(e) => {
            warn!(error = %e, "Failed to load export source");
            Ok(HashMap::new())
        }
    }
}
