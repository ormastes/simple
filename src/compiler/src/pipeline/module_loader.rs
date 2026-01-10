//! Module loading and import resolution utilities.

use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

use simple_parser::ast::{Argument, Capability, Effect, Expr, ImportTarget, Module, Node, UseStmt};

use crate::CompileError;

/// Application type for startup optimization (#1979)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum StartupAppType {
    /// Command-line tool (minimal resources)
    #[default]
    Cli,
    /// Terminal UI application (terminal mode, buffers)
    Tui,
    /// Graphical application (window, GPU context)
    Gui,
    /// Background service/daemon (IPC, signal handlers)
    Service,
    /// Interactive REPL (history, line editor)
    Repl,
}

impl StartupAppType {
    /// Parse from string
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "cli" => Some(Self::Cli),
            "tui" => Some(Self::Tui),
            "gui" => Some(Self::Gui),
            "service" => Some(Self::Service),
            "repl" => Some(Self::Repl),
            _ => None,
        }
    }

    /// Convert to u8 for SMF header
    pub fn to_smf_byte(self) -> u8 {
        match self {
            Self::Cli => 0,
            Self::Tui => 1,
            Self::Gui => 2,
            Self::Service => 3,
            Self::Repl => 4,
        }
    }
}

/// Window hints for GUI applications (#1986)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StartupWindowHints {
    pub width: u16,
    pub height: u16,
    pub title: String,
}

impl Default for StartupWindowHints {
    fn default() -> Self {
        Self {
            width: 1280,
            height: 720,
            title: "Simple Application".to_string(),
        }
    }
}

/// Startup configuration extracted from module decorators (#1979, #1986)
#[derive(Debug, Clone, Default)]
pub struct StartupConfig {
    /// Application type from @app_type decorator
    pub app_type: StartupAppType,
    /// Window hints from @window_hints decorator
    pub window_hints: StartupWindowHints,
    /// Whether @app_type was explicitly set
    pub has_app_type: bool,
    /// Whether @window_hints was explicitly set
    pub has_window_hints: bool,
}

/// Extract startup configuration from a module's main function decorators.
///
/// Looks for:
/// - `@app_type("gui")` - application type
/// - `@window_hints(width=1920, height=1080, title="My App")` - window configuration
///
/// Returns None if no main function found.
pub fn extract_startup_config(module: &Module) -> Option<StartupConfig> {
    // Find the main function
    for item in &module.items {
        if let Node::Function(func) = item {
            if func.name == "main" {
                return Some(extract_startup_config_from_decorators(&func.decorators));
            }
        }
    }
    None
}

/// Extract startup configuration from a list of decorators.
fn extract_startup_config_from_decorators(
    decorators: &[simple_parser::ast::Decorator],
) -> StartupConfig {
    let mut config = StartupConfig::default();

    for decorator in decorators {
        // Check decorator name
        let name = match &decorator.name {
            Expr::Identifier(name) => name.as_str(),
            _ => continue,
        };

        match name {
            "app_type" => {
                // @app_type("gui") - first positional argument is the type
                if let Some(args) = &decorator.args {
                    if let Some(first_arg) = args.first() {
                        if let Some(type_str) = extract_string_from_arg(first_arg) {
                            if let Some(app_type) = StartupAppType::from_str(&type_str) {
                                config.app_type = app_type;
                                config.has_app_type = true;
                            }
                        }
                    }
                }
            }
            "window_hints" => {
                // @window_hints(width=1920, height=1080, title="My App")
                if let Some(args) = &decorator.args {
                    for arg in args {
                        // Argument is a struct with name: Option<String> and value: Expr
                        if let Some(arg_name) = &arg.name {
                            match arg_name.as_str() {
                                "width" => {
                                    if let Some(w) = extract_integer_from_expr(&arg.value) {
                                        config.window_hints.width = w as u16;
                                        config.has_window_hints = true;
                                    }
                                }
                                "height" => {
                                    if let Some(h) = extract_integer_from_expr(&arg.value) {
                                        config.window_hints.height = h as u16;
                                        config.has_window_hints = true;
                                    }
                                }
                                "title" => {
                                    if let Some(t) = extract_string_from_expr(&arg.value) {
                                        config.window_hints.title = t;
                                        config.has_window_hints = true;
                                    }
                                }
                                _ => {}
                            }
                        }
                        // Ignore positional args for window_hints
                    }
                }
            }
            _ => {}
        }
    }

    config
}

/// Extract string value from an argument
fn extract_string_from_arg(arg: &Argument) -> Option<String> {
    extract_string_from_expr(&arg.value)
}

/// Extract string value from an expression
fn extract_string_from_expr(expr: &Expr) -> Option<String> {
    match expr {
        Expr::String(s) => Some(s.clone()),
        Expr::TypedString(s, _) => Some(s.clone()),
        // Handle FString (interpolated strings) - extract if it's just a literal
        Expr::FString(parts) => {
            if parts.len() == 1 {
                if let simple_parser::ast::FStringPart::Literal(s) = &parts[0] {
                    return Some(s.clone());
                }
            }
            None
        }
        _ => None,
    }
}

/// Extract integer value from an expression
fn extract_integer_from_expr(expr: &Expr) -> Option<i64> {
    match expr {
        Expr::Integer(n) => Some(*n),
        Expr::TypedInteger(n, _) => Some(*n),
        _ => None,
    }
}

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
            Effect::Async => None,   // Async is always allowed
            Effect::Verify => None,  // Verification mode marker, no capability
            Effect::Trusted => None, // Trusted boundary marker, no capability
            Effect::Ghost => None,   // Ghost is compile-time only, no capability
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
                let imported =
                    load_module_with_imports_validated(&resolved, visited, Some(effective_caps))?;

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

                // Add imported items for flattened access (functions/classes in global scope)
                items.extend(imported.items);
                // ALSO keep the UseStmt so evaluate_module can create the module binding
                // The module exports cache prevents redundant re-parsing
                items.push(item);
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
/// Also checks stdlib location if sibling resolution fails.
fn resolve_use_to_path(use_stmt: &UseStmt, base: &Path) -> Option<PathBuf> {
    let mut parts: Vec<String> = use_stmt
        .path
        .segments
        .iter()
        .filter(|s| s.as_str() != "crate")
        .cloned()
        .collect();

    // For symbol-specific imports (Single, Aliased, Group), we want to resolve
    // to the MODULE file (not to a per-symbol file). The path segments already
    // contain the module path. Only for Glob do we use the path as-is.
    match &use_stmt.target {
        ImportTarget::Single(_) | ImportTarget::Aliased { .. } | ImportTarget::Group(_) => {
            // Symbol-specific import: resolve to the module file
            // e.g., `import test_import_a.{SimpleError}` -> resolve to test_import_a.spl
            // The parts already contain just the module path (test_import_a)
        }
        ImportTarget::Glob => {
            // For glob imports like `use ui.element.*`, the path segments
            // already contain the module path, we just resolve it as-is
            // (the last segment is the module file)
        }
    }

    // Try resolving from base directory first (sibling files)
    let mut resolved = base.to_path_buf();
    for part in &parts {
        resolved = resolved.join(part);
    }
    resolved.set_extension("spl");
    if resolved.exists() {
        return Some(resolved);
    }

    // Try __init__.spl in directory (Python-style package imports)
    let mut init_resolved = base.to_path_buf();
    for part in &parts {
        init_resolved = init_resolved.join(part);
    }
    init_resolved = init_resolved.join("__init__");
    init_resolved.set_extension("spl");
    if init_resolved.exists() {
        return Some(init_resolved);
    }

    // If not found, try stdlib location
    // Walk up the directory tree to find std_lib/src
    let mut current = base.to_path_buf();
    for _ in 0..5 {
        // Check if current path ends with std_lib/src - if so, use it directly
        let stdlib_candidate = if current.ends_with("std_lib/src") {
            current.clone()
        } else {
            current.join("simple/std_lib/src")
        };

        if stdlib_candidate.exists() {
            // Try resolving from stdlib
            let mut stdlib_path = stdlib_candidate.clone();
            for part in &parts {
                stdlib_path = stdlib_path.join(part);
            }
            stdlib_path.set_extension("spl");
            if stdlib_path.exists() {
                return Some(stdlib_path);
            }

            // Also try __init__.spl in stdlib
            let mut stdlib_init_path = stdlib_candidate.clone();
            for part in &parts {
                stdlib_init_path = stdlib_init_path.join(part);
            }
            stdlib_init_path = stdlib_init_path.join("__init__");
            stdlib_init_path.set_extension("spl");
            if stdlib_init_path.exists() {
                return Some(stdlib_init_path);
            }
        }
        if let Some(parent) = current.parent() {
            current = parent.to_path_buf();
        } else {
            break;
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_startup_app_type_parsing() {
        assert_eq!(StartupAppType::from_str("cli"), Some(StartupAppType::Cli));
        assert_eq!(StartupAppType::from_str("tui"), Some(StartupAppType::Tui));
        assert_eq!(StartupAppType::from_str("gui"), Some(StartupAppType::Gui));
        assert_eq!(
            StartupAppType::from_str("service"),
            Some(StartupAppType::Service)
        );
        assert_eq!(StartupAppType::from_str("repl"), Some(StartupAppType::Repl));
        assert_eq!(StartupAppType::from_str("GUI"), Some(StartupAppType::Gui)); // Case insensitive
        assert_eq!(StartupAppType::from_str("invalid"), None);
    }

    #[test]
    fn test_startup_app_type_to_smf_byte() {
        assert_eq!(StartupAppType::Cli.to_smf_byte(), 0);
        assert_eq!(StartupAppType::Tui.to_smf_byte(), 1);
        assert_eq!(StartupAppType::Gui.to_smf_byte(), 2);
        assert_eq!(StartupAppType::Service.to_smf_byte(), 3);
        assert_eq!(StartupAppType::Repl.to_smf_byte(), 4);
    }

    #[test]
    fn test_startup_window_hints_default() {
        let hints = StartupWindowHints::default();
        assert_eq!(hints.width, 1280);
        assert_eq!(hints.height, 720);
        assert_eq!(hints.title, "Simple Application");
    }

    #[test]
    fn test_startup_config_default() {
        let config = StartupConfig::default();
        assert_eq!(config.app_type, StartupAppType::Cli);
        assert!(!config.has_app_type);
        assert!(!config.has_window_hints);
    }

    #[test]
    fn test_extract_startup_config_with_app_type() {
        let source = r#"
@app_type("gui")
fn main():
    pass
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");
        let config = extract_startup_config(&module);

        assert!(config.is_some());
        let config = config.unwrap();
        assert_eq!(config.app_type, StartupAppType::Gui);
        assert!(config.has_app_type);
    }

    #[test]
    fn test_extract_startup_config_with_window_hints() {
        let source = r#"
@window_hints(width=1920, height=1080, title="Test App")
fn main():
    pass
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");
        let config = extract_startup_config(&module);

        assert!(config.is_some());
        let config = config.unwrap();
        assert_eq!(config.window_hints.width, 1920);
        assert_eq!(config.window_hints.height, 1080);
        assert_eq!(config.window_hints.title, "Test App");
        assert!(config.has_window_hints);
    }

    #[test]
    fn test_extract_startup_config_combined() {
        let source = r#"
@app_type("gui")
@window_hints(width=800, height=600, title="My Game")
fn main():
    pass
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");
        let config = extract_startup_config(&module);

        assert!(config.is_some());
        let config = config.unwrap();
        assert_eq!(config.app_type, StartupAppType::Gui);
        assert!(config.has_app_type);
        assert_eq!(config.window_hints.width, 800);
        assert_eq!(config.window_hints.height, 600);
        assert_eq!(config.window_hints.title, "My Game");
        assert!(config.has_window_hints);
    }

    #[test]
    fn test_extract_startup_config_no_main() {
        let source = r#"
fn other():
    pass
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");
        let config = extract_startup_config(&module);

        assert!(config.is_none());
    }

    #[test]
    fn test_extract_startup_config_main_no_decorators() {
        let source = r#"
fn main():
    pass
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");
        let config = extract_startup_config(&module);

        assert!(config.is_some());
        let config = config.unwrap();
        assert_eq!(config.app_type, StartupAppType::Cli); // Default
        assert!(!config.has_app_type);
        assert!(!config.has_window_hints);
    }

    #[test]
    fn test_extract_startup_config_partial_window_hints() {
        let source = r#"
@window_hints(width=1600)
fn main():
    pass
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");
        let config = extract_startup_config(&module);

        assert!(config.is_some());
        let config = config.unwrap();
        assert_eq!(config.window_hints.width, 1600);
        assert_eq!(config.window_hints.height, 720); // Default
        assert_eq!(config.window_hints.title, "Simple Application"); // Default
        assert!(config.has_window_hints);
    }
}
