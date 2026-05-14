use super::{find_simple_workspace_root, CheckError, ErrorSeverity};
use simple_parser::ast::{ImportTarget, ModulePath, Node};
use simple_parser::Parser;
use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug, Clone)]
struct NoallocRoots {
    noalloc: PathBuf,
    common: PathBuf,
}

#[derive(Debug)]
struct ImportEdge {
    line: usize,
    column: usize,
    module: String,
    path: ModulePath,
    target: ImportTarget,
}

const NOALLOC_FAMILY: &str = "nogc_async_mut_noalloc";

pub(super) fn validate_noalloc_reachable_import_closure(
    file_path: &Path,
    errors: &mut Vec<CheckError>,
    source_roots: &[PathBuf],
    deny_gc_boundary_crossings: bool,
) {
    if !deny_gc_boundary_crossings {
        return;
    }

    let abs_path = absolute_path(file_path);
    let Some(roots) = noalloc_roots_for_file(&abs_path, source_roots) else {
        return;
    };

    let mut queue = vec![abs_path];
    let mut seen = HashSet::new();

    while let Some(path) = queue.pop() {
        let path = absolute_path(&path);
        if !seen.insert(path.clone()) {
            continue;
        }

        let source = match fs::read_to_string(&path) {
            Ok(source) => source,
            Err(_) => continue,
        };

        validate_noalloc_source_text(&path, &source, errors);

        let mut parser = Parser::new(&source);
        let Ok(module) = parser.parse() else {
            continue;
        };

        for import in noalloc_import_edges(&module.items) {
            if is_forbidden_noalloc_module(&import.module) {
                push_noalloc_check_error(
                    errors,
                    &path,
                    import.line,
                    import.column,
                    format!(
                        "noalloc reachable import '{}' crosses into an allocating or host runtime family",
                        import.module
                    ),
                    vec!["keep noalloc closures within std.nogc_async_mut_noalloc and std.common".to_string()],
                );
                continue;
            }

            let Some(resolved) = resolve_noalloc_import(&roots, &path, &import.path, &import.target) else {
                continue;
            };

            if !is_path_within(&resolved, &roots.noalloc) && !is_path_within(&resolved, &roots.common) {
                push_noalloc_check_error(
                    errors,
                    &path,
                    import.line,
                    import.column,
                    format!(
                        "noalloc reachable import '{}' resolves outside the allowed noalloc/common roots",
                        import.module
                    ),
                    vec![format!("resolved path: {}", resolved.display())],
                );
                continue;
            }

            if !seen.contains(&resolved) {
                queue.push(resolved);
            }
        }
    }
}

fn absolute_path(path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .map(|cwd| cwd.join(path))
            .unwrap_or_else(|_| path.to_path_buf())
    }
}

fn noalloc_roots_for_file(file_path: &Path, source_roots: &[PathBuf]) -> Option<NoallocRoots> {
    for lib_root in candidate_lib_roots(file_path, source_roots) {
        let noalloc = lib_root.join(NOALLOC_FAMILY);
        if is_path_within(file_path, &noalloc) {
            return Some(NoallocRoots {
                noalloc,
                common: lib_root.join("common"),
            });
        }
    }

    None
}

fn candidate_lib_roots(file_path: &Path, source_roots: &[PathBuf]) -> Vec<PathBuf> {
    let mut roots = Vec::new();
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

    for source_root in source_roots {
        roots.push(if source_root.is_absolute() {
            source_root.clone()
        } else {
            cwd.join(source_root)
        });
    }

    if let Some(lib_root) = lib_root_from_path(file_path) {
        roots.push(lib_root);
    }

    if let Some(workspace_root) = find_simple_workspace_root(file_path) {
        roots.push(workspace_root.join("src/lib"));
    }

    roots.sort();
    roots.dedup();
    roots
}

fn lib_root_from_path(file_path: &Path) -> Option<PathBuf> {
    let components = file_path.components().collect::<Vec<_>>();
    for index in 0..components.len().saturating_sub(2) {
        if components[index].as_os_str() == "src"
            && components[index + 1].as_os_str() == "lib"
            && components[index + 2].as_os_str() == NOALLOC_FAMILY
        {
            let mut root = PathBuf::new();
            for component in &components[..index + 2] {
                root.push(component.as_os_str());
            }
            return Some(root);
        }
    }

    None
}

fn validate_noalloc_source_text(file_path: &Path, source: &str, errors: &mut Vec<CheckError>) {
    for (line_index, line) in source.lines().enumerate() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("@alloc") || trimmed.starts_with("# @alloc") || trimmed.starts_with("#@alloc") {
            push_noalloc_check_error(
                errors,
                file_path,
                line_index + 1,
                line.len() - trimmed.len() + 1,
                "allocation annotation is reachable from a noalloc closure".to_string(),
                vec!["move allocating APIs to a GC/runtime-family facade outside the noalloc backend".to_string()],
            );
        }

        if line.contains("malloc(") || line.contains("calloc(") || line.contains("free(") || line.contains("rt_alloc") {
            push_noalloc_check_error(
                errors,
                file_path,
                line_index + 1,
                1,
                "host allocation API is reachable from a noalloc closure".to_string(),
                vec!["noalloc backend code must use caller-provided storage or explicit backend handles".to_string()],
            );
        }
    }
}

fn noalloc_import_edges(items: &[Node]) -> Vec<ImportEdge> {
    let mut edges = Vec::new();
    for item in items {
        match item {
            Node::UseStmt(stmt) => edges.push(ImportEdge {
                line: stmt.span.line,
                column: stmt.span.column,
                module: display_import_module(&stmt.path, &stmt.target),
                path: stmt.path.clone(),
                target: stmt.target.clone(),
            }),
            Node::CommonUseStmt(stmt) => edges.push(ImportEdge {
                line: stmt.span.line,
                column: stmt.span.column,
                module: display_import_module(&stmt.path, &stmt.target),
                path: stmt.path.clone(),
                target: stmt.target.clone(),
            }),
            Node::ExportUseStmt(stmt) => edges.push(ImportEdge {
                line: stmt.span.line,
                column: stmt.span.column,
                module: display_import_module(&stmt.path, &stmt.target),
                path: stmt.path.clone(),
                target: stmt.target.clone(),
            }),
            _ => {}
        }
    }
    edges
}

fn display_import_module(module_path: &ModulePath, target: &ImportTarget) -> String {
    target_module_path(module_path, target)
        .unwrap_or_else(|| module_path.clone())
        .segments
        .join(".")
}

fn is_forbidden_noalloc_module(module: &str) -> bool {
    [
        "std.nogc_sync_mut.",
        "std.nogc_async_mut.",
        "std.nogc_async_immut.",
        "std.gc_async_mut.",
        "std.posix.",
        "std.linux.",
        "posix.",
        "linux.",
        "os.",
        "app.",
        "examples.",
    ]
    .iter()
    .any(|prefix| module.starts_with(prefix))
}

fn resolve_noalloc_import(
    roots: &NoallocRoots,
    current_file: &Path,
    module_path: &ModulePath,
    target: &ImportTarget,
) -> Option<PathBuf> {
    let mut candidates = Vec::new();
    candidates.extend(noalloc_module_candidates(roots, &module_path.segments, current_file));

    if let Some(target_path) = target_module_path(module_path, target) {
        candidates.extend(noalloc_module_candidates(roots, &target_path.segments, current_file));
    }

    candidates.into_iter().find_map(existing_noalloc_candidate)
}

fn target_module_path(module_path: &ModulePath, target: &ImportTarget) -> Option<ModulePath> {
    match target {
        ImportTarget::Single(name) | ImportTarget::Aliased { name, .. } => {
            let mut segments = module_path.segments.clone();
            segments.push(name.clone());
            Some(ModulePath::new(segments))
        }
        _ => None,
    }
}

fn noalloc_module_candidates(roots: &NoallocRoots, segments: &[String], current_file: &Path) -> Vec<PathBuf> {
    if segments.is_empty() {
        return Vec::new();
    }

    let mut candidates = Vec::new();
    let first = segments[0].as_str();
    let second = segments.get(1).map(String::as_str);

    if first == "std" || first == "lib" {
        match second {
            Some(NOALLOC_FAMILY) => candidates.push(roots.noalloc.join(PathBuf::from_iter(&segments[2..]))),
            Some("common") => candidates.push(roots.common.join(PathBuf::from_iter(&segments[2..]))),
            Some(_) if first == "std" => {
                candidates.push(roots.noalloc.join(PathBuf::from_iter(&segments[1..])));
                candidates.push(roots.common.join(PathBuf::from_iter(&segments[1..])));
            }
            _ => {}
        }
    } else if first == "common" {
        candidates.push(roots.common.join(PathBuf::from_iter(&segments[1..])));
    } else {
        candidates.push(
            current_file
                .parent()
                .unwrap_or_else(|| Path::new("."))
                .join(PathBuf::from_iter(segments)),
        );
    }

    candidates
}

fn existing_noalloc_candidate(path: PathBuf) -> Option<PathBuf> {
    let file = path.with_extension("spl");
    if file.is_file() {
        return Some(file);
    }

    let init = path.join("__init__.spl");
    if init.is_file() {
        return Some(init);
    }

    None
}

fn is_path_within(path: &Path, root: &Path) -> bool {
    let path = absolute_path(path);
    let root = absolute_path(root);
    path.starts_with(root)
}

fn push_noalloc_check_error(
    errors: &mut Vec<CheckError>,
    file_path: &Path,
    line: usize,
    column: usize,
    message: String,
    help: Vec<String>,
) {
    let file = file_path.display().to_string();
    if errors.iter().any(|error| {
        error.code.as_deref() == Some("E0413")
            && error.file == file
            && error.line == line
            && error.column == column
            && error.message == message
    }) {
        return;
    }

    errors.push(noalloc_check_error(file_path, line, column, message, help));
}

fn noalloc_check_error(file_path: &Path, line: usize, column: usize, message: String, help: Vec<String>) -> CheckError {
    CheckError {
        file: file_path.display().to_string(),
        line,
        column,
        severity: ErrorSeverity::Error,
        code: Some("E0413".to_string()),
        message,
        expected: Some("nogc_async_mut_noalloc/common reachable imports only".to_string()),
        found: None,
        notes: Vec::new(),
        help,
    }
}
