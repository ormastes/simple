//! Module import loading and resolution utilities.

use std::collections::HashSet;
use std::fs;
use std::path::Path;

use crate::CompileError;

/// Detect whether the module contains script-style statements (non-item code) at the top level.
/// These should be interpreted directly rather than lowered through HIR/MIR.
pub(crate) fn has_script_statements(items: &[simple_parser::ast::Node]) -> bool {
    use simple_parser::ast::Node::*;
    items.iter().any(|item| {
        matches!(
            item,
            Let(_)
                | Const(_)
                | Static(_)
                | Assignment(_)
                | Return(_)
                | If(_)
                | Match(_)
                | For(_)
                | While(_)
                | Loop(_)
                | Break(_)
                | Continue(_)
                | Context(_)
                | With(_)
                | Expression(_)
        )
    })
}

/// Naive resolver for `use foo` when running single-file programs from the CLI.
/// Recursively loads sibling modules and flattens their items into the root module.
pub(crate) fn load_module_with_imports(
    path: &Path,
    visited: &mut HashSet<std::path::PathBuf>,
) -> Result<simple_parser::ast::Module, CompileError> {
    let path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    if !visited.insert(path.clone()) {
        return Ok(simple_parser::ast::Module {
            name: None,
            items: Vec::new(),
        });
    }

    let source = fs::read_to_string(&path).map_err(|e| CompileError::Io(format!("{e}")))?;
    let mut parser = simple_parser::Parser::new(&source);
    let module = parser
        .parse()
        .map_err(|e| CompileError::Parse(format!("{e}")))?;

    let mut items = Vec::new();
    for item in module.items {
        if let simple_parser::ast::Node::UseStmt(use_stmt) = &item {
            if let Some(resolved) =
                resolve_use_to_path(use_stmt, path.parent().unwrap_or(Path::new(".")))
            {
                let imported = load_module_with_imports(&resolved, visited)?;
                items.extend(imported.items);
                continue;
            }
        }
        items.push(item);
    }

    Ok(simple_parser::ast::Module {
        name: module.name,
        items,
    })
}

/// Resolve a simple `use` path to a sibling `.spl` file.
fn resolve_use_to_path(
    use_stmt: &simple_parser::ast::UseStmt,
    base: &Path,
) -> Option<std::path::PathBuf> {
    use simple_parser::ast::ImportTarget;
    let mut parts: Vec<String> = use_stmt
        .path
        .segments
        .iter()
        .filter(|s| s.as_str() != "crate")
        .cloned()
        .collect();

    let target_name = match &use_stmt.target {
        ImportTarget::Single(name) => Some(name.clone()),
        ImportTarget::Aliased { name, .. } => Some(name.clone()),
        _ => None,
    }?;

    parts.push(target_name);
    let mut resolved = base.to_path_buf();
    for part in parts {
        resolved = resolved.join(part);
    }
    resolved.set_extension("spl");
    if resolved.exists() {
        Some(resolved)
    } else {
        None
    }
}
