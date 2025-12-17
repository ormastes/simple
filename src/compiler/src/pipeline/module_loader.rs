//! Module loading and import resolution utilities.

use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

use simple_parser::ast::{Capability, Effect, ImportTarget, Module, Node, UseStmt};

use crate::CompileError;

/// Extract capabilities from a module's `requires [...]` statement.
/// Returns None if no requires statement found (unrestricted module).
pub fn extract_module_capabilities(module: &Module) -> Option<Vec<Capability>> {
    for item in &module.items {
        if let Node::RequiresCapabilities(stmt) = item {
            return Some(stmt.capabilities.clone());
        }
    }
    None
}

/// Extract function effects from a module.
/// Returns a list of (function_name, effects) pairs.
pub fn extract_function_effects(module: &Module) -> Vec<(String, Vec<Effect>)> {
    let mut results = Vec::new();
    for item in &module.items {
        if let Node::Function(func) = item {
            if !func.effects.is_empty() {
                results.push((func.name.clone(), func.effects.clone()));
            }
        }
    }
    results
}

/// Check if a function's effects are compatible with a module's capabilities.
/// Returns an error message if incompatible, None if compatible.
pub fn check_import_compatibility(
    func_name: &str,
    func_effects: &[Effect],
    importing_capabilities: &[Capability],
) -> Option<String> {
    // If importing module is unrestricted, all imports are allowed
    if importing_capabilities.is_empty() {
        return None;
    }

    for effect in func_effects {
        let required_cap = match effect {
            Effect::Pure => Some(Capability::Pure),
            Effect::Io => Some(Capability::Io),
            Effect::Net => Some(Capability::Net),
            Effect::Fs => Some(Capability::Fs),
            Effect::Unsafe => Some(Capability::Unsafe),
            Effect::Async => None, // Async is always allowed
        };

        if let Some(cap) = required_cap {
            if !importing_capabilities.contains(&cap) {
                return Some(format!(
                    "cannot import function '{}' with @{} effect into module with capabilities [{}]",
                    func_name,
                    effect.decorator_name(),
                    importing_capabilities
                        .iter()
                        .map(|c| c.name())
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
        }
    }

    None
}

/// Naive resolver for `use foo` when running single-file programs from the CLI.
///
/// Recursively loads sibling modules and flattens their items into the root module.
pub fn load_module_with_imports(
    path: &Path,
    visited: &mut HashSet<PathBuf>,
) -> Result<Module, CompileError> {
    load_module_with_imports_validated(path, visited, None)
}

/// Load module with imports and validate imported function effects against capabilities.
///
/// If `importing_capabilities` is Some, validates that imported functions have effects
/// compatible with the importing module's capabilities.
pub fn load_module_with_imports_validated(
    path: &Path,
    visited: &mut HashSet<PathBuf>,
    importing_capabilities: Option<&[Capability]>,
) -> Result<Module, CompileError> {
    let path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    if !visited.insert(path.clone()) {
        return Ok(Module {
            name: None,
            items: Vec::new(),
        });
    }

    let source = fs::read_to_string(&path).map_err(|e| CompileError::Io(format!("{e}")))?;
    let mut parser = simple_parser::Parser::new(&source);
    let module = parser
        .parse()
        .map_err(|e| CompileError::Parse(format!("{e}")))?;

    // Extract this module's capabilities for passing to child imports
    let this_caps = extract_module_capabilities(&module);
    let effective_caps = importing_capabilities
        .or(this_caps.as_deref())
        .unwrap_or(&[]);

    let mut items = Vec::new();
    for item in module.items {
        if let Node::UseStmt(use_stmt) = &item {
            if let Some(resolved) =
                resolve_use_to_path(use_stmt, path.parent().unwrap_or(Path::new(".")))
            {
                let imported = load_module_with_imports_validated(
                    &resolved,
                    visited,
                    Some(effective_caps),
                )?;

                // Validate imported functions against our capabilities
                if !effective_caps.is_empty() {
                    let func_effects = extract_function_effects(&imported);
                    for (func_name, effects) in func_effects {
                        if let Some(err) =
                            check_import_compatibility(&func_name, &effects, effective_caps)
                        {
                            return Err(CompileError::Semantic(err));
                        }
                    }
                }

                items.extend(imported.items);
                continue;
            }
        }
        items.push(item);
    }

    Ok(Module {
        name: module.name,
        items,
    })
}

/// Resolve a simple `use` path to a sibling `.spl` file.
fn resolve_use_to_path(use_stmt: &UseStmt, base: &Path) -> Option<PathBuf> {
    let mut parts: Vec<String> = use_stmt
        .path
        .segments
        .iter()
        .filter(|s| s.as_str() != "crate")
        .cloned()
        .collect();

    // Handle different import targets
    match &use_stmt.target {
        ImportTarget::Single(name) => {
            parts.push(name.clone());
        }
        ImportTarget::Aliased { name, .. } => {
            parts.push(name.clone());
        }
        ImportTarget::Glob => {
            // For glob imports like `use ui.element.*`, the path segments
            // already contain the module path, we just resolve it as-is
            // (the last segment is the module file)
        }
        ImportTarget::Group(_) => {
            // Group imports need special handling - for now, skip them
            return None;
        }
    }

    let mut resolved = base.to_path_buf();
    for part in &parts {
        resolved = resolved.join(part);
    }
    resolved.set_extension("spl");
    if resolved.exists() {
        Some(resolved)
    } else {
        None
    }
}
