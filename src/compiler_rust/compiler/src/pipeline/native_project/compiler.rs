//! File compilation pipeline: parse, lower, codegen, parallel/sequential dispatch.

use std::path::{Path, PathBuf};
use std::time::Duration;

use rayon::prelude::*;

use crate::codegen::common_backend::module_prefix_from_path;
use crate::codegen::Codegen;
use crate::hir::Lowerer;
use crate::module_resolver::ModuleResolver;
use crate::monomorphize::monomorphize_module;

use super::{effective_target, is_entry_file, safe_canonicalize, source_root_for_file, ModuleImports, NativeProjectBuilder};
use super::imports::{build_suffix_index, build_use_map_from_ast};
use super::mangle::mangle_mir;

impl NativeProjectBuilder {
    /// Compile entries (index, path, source) in parallel using rayon.
    pub(crate) fn compile_entries_parallel(
        &self,
        entries: &[(usize, PathBuf, String)],
        temp_dir: &Path,
        canonical_entry: &Option<PathBuf>,
        imports: &ModuleImports,
    ) -> Vec<Result<(usize, PathBuf), (PathBuf, String)>> {
        // Configure rayon thread pool if needed
        if let Some(n) = self.config.num_threads {
            let _ = rayon::ThreadPoolBuilder::new().num_threads(n).build_global();
        }

        let project_root = self.project_root.clone();
        let source_dirs = self.source_dirs.clone();
        let fallback_root = self.source_root.clone();
        let file_timeout = self.config.file_timeout;
        let stack_size = self.config.stack_size;
        let verbose = self.config.verbose;
        let temp_dir = temp_dir.to_path_buf();
        let total = entries.len();
        let no_mangle = self.config.no_mangle;
        let canonical_entry = canonical_entry.clone();
        let imports = imports.clone();

        entries
            .par_iter()
            .enumerate()
            .map(|(progress_i, (idx, path, source))| {
                let is_entry = is_entry_file(path, &canonical_entry);
                if verbose && is_entry {
                    eprintln!("  [entry] {}", path.display());
                }
                match compile_file_safe(
                    source.clone(),
                    path.clone(),
                    project_root.clone(),
                    source_dirs.clone(),
                    fallback_root.clone(),
                    file_timeout,
                    stack_size,
                    no_mangle,
                    is_entry,
                    imports.clone(),
                ) {
                    Ok(obj_code) => {
                        let obj_path = temp_dir.join(format!("mod_{}.o", idx));
                        std::fs::write(&obj_path, &obj_code).map_err(|e| (path.clone(), format!("write .o: {e}")))?;
                        if verbose && (progress_i + 1) % 50 == 0 {
                            eprintln!("  [{}/{}] compiled", progress_i + 1, total);
                        }
                        Ok((*idx, obj_path))
                    }
                    Err(e) => {
                        let msg = format!("{}: {}", path.display(), e);
                        Err((path.clone(), msg))
                    }
                }
            })
            .collect()
    }

    /// Compile entries sequentially (fallback).
    pub(crate) fn compile_entries_sequential(
        &self,
        entries: &[(usize, PathBuf, String)],
        temp_dir: &Path,
        canonical_entry: &Option<PathBuf>,
        imports: &ModuleImports,
    ) -> Vec<Result<(usize, PathBuf), (PathBuf, String)>> {
        let total = entries.len();
        entries
            .iter()
            .enumerate()
            .map(|(progress_i, (idx, path, source))| {
                let is_entry = is_entry_file(path, canonical_entry);
                if self.config.verbose && is_entry {
                    eprintln!("  [entry] {}", path.display());
                }
                match compile_file_safe(
                    source.clone(),
                    path.clone(),
                    self.project_root.clone(),
                    self.source_dirs.clone(),
                    self.source_root.clone(),
                    self.config.file_timeout,
                    self.config.stack_size,
                    self.config.no_mangle,
                    is_entry,
                    imports.clone(),
                ) {
                    Ok(obj_code) => {
                        let obj_path = temp_dir.join(format!("mod_{}.o", idx));
                        std::fs::write(&obj_path, &obj_code).map_err(|e| (path.clone(), format!("write .o: {e}")))?;
                        if self.config.verbose && (progress_i + 1) % 10 == 0 {
                            eprintln!("  [{}/{}] compiled", progress_i + 1, total);
                        }
                        Ok((*idx, obj_path))
                    }
                    Err(e) => {
                        let msg = format!("{}: {}", path.display(), e);
                        Err((path.clone(), msg))
                    }
                }
            })
            .collect()
    }
}

/// Compile a single .spl file to object code.
pub(crate) fn compile_file_to_object(
    source: &str,
    file_path: &Path,
    project_root: &Path,
    source_root: &Path,
    source_dirs: &[PathBuf],
    no_mangle: bool,
    is_entry: bool,
    imports: &ModuleImports,
) -> Result<Vec<u8>, String> {
    // Bootstrap hack: normalize optional types that older lenient type resolver misses
    let is_bootstrap = std::env::var("SIMPLE_BOOTSTRAP").as_deref() == Ok("1");
    let mut source = if is_bootstrap {
        apply_bootstrap_rewrite(source)
    } else {
        // Non-bootstrap: just normalize text? -> text for basic compat
        source.replace("text?", "text")
    };

    // Parse
    let mut parser = simple_parser::Parser::new(&source);
    let ast = parser
        .parse()
        .map_err(|e| format!("{}: parse: {e}", file_path.display()))?;

    // Build per-module use_map from AST `use` statements.
    let use_map = build_use_map_from_ast(&ast, &imports.all_mangled, &imports.re_exports);

    // Mono
    let ast = monomorphize_module(&ast);

    // HIR
    let hir_source_root = source_root.to_path_buf();
    let resolver =
        ModuleResolver::new(project_root.to_path_buf(), hir_source_root).with_extra_source_roots(source_dirs.to_vec());
    let mut lowerer = Lowerer::with_module_resolver(resolver, file_path.to_path_buf());
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    // Pass the global struct defs to the lowerer so cross-module field access
    // can resolve to a FieldGet instead of a dynamic method call.
    //
    // Historically this was filtered down to single-field wrappers only,
    // because the naive "pick the struct with the most fields" heuristic in
    // `get_field_info` would silently return the wrong byte offset when two
    // unrelated structs shared a field name (the BeDomNode/BeLayoutBox
    // `children` collision, cf800979c6). But that filter also broke every
    // multi-field struct that crosses a module boundary — e.g.
    // `McpToolEntry` in `src/app/mcp/` whose callers live in a sibling file
    // that doesn't explicitly `use` the type, so the HIR lowerer sees the
    // receiver as ANY and the resolution falls through to a method call
    // that links to nothing (`Function 'props_json' not found`).
    //
    // We now pass ALL multi-field struct defs through as well. To avoid the
    // BeDomNode ambiguity the lowerer also receives an `ambiguous_field_names`
    // set — any name defined by more than one struct is blacklisted and
    // falls back to a method call there, which is exactly what the old
    // single-field filter was protecting. Unambiguous fields get a real
    // byte-offset load, which is what McpToolEntry needs.
    //
    // Gated on `--entry-closure` to avoid any risk to self-host bootstrap.
    if imports.populate_global_struct_defs {
        use std::collections::{HashMap, HashSet};
        // A field name is ambiguous *only* when two structs disagree on its
        // index within the struct. Two structs that both put `name` at index
        // 0 produce the same byte offset (0), so picking either struct is
        // harmless — that's the McpToolEntry / T32DialogItem case, and the
        // old "any duplication is ambiguous" rule was breaking it.
        // The case the rule has to catch is the BeDomNode/BeLayoutBox bug
        // where `children` is at index 3 in one struct and index 7 in the
        // other; picking the wrong struct would silently load the wrong
        // memory location.
        let mut field_indices: HashMap<String, HashSet<usize>> = HashMap::new();
        for fields in imports.struct_defs.values() {
            for (idx, (fname, _)) in fields.iter().enumerate() {
                field_indices.entry(fname.clone()).or_default().insert(idx);
            }
        }
        let ambiguous: HashSet<String> = field_indices
            .into_iter()
            .filter_map(|(name, indices)| if indices.len() > 1 { Some(name) } else { None })
            .collect();
        lowerer.set_global_struct_defs(std::sync::Arc::new((*imports.struct_defs).clone()));
        lowerer.set_ambiguous_field_names(std::sync::Arc::new(ambiguous));
    } else {
        lowerer.set_global_struct_defs(std::sync::Arc::new(std::collections::HashMap::new()));
        lowerer.set_ambiguous_field_names(std::sync::Arc::new(std::collections::HashSet::new()));
    }
    let hir = lowerer
        .lower_module(&ast)
        .map_err(|e| format!("{}: hir: {e}", file_path.display()))?;

    // MIR
    let mir = crate::mir::lower_to_mir(&hir).map_err(|e| format!("{}: mir: {e}", file_path.display()))?;

    // Codegen -- select backend via SIMPLE_BACKEND env var
    let use_llvm = std::env::var("SIMPLE_BACKEND").as_deref() == Ok("llvm");

    if use_llvm {
        #[cfg(feature = "llvm")]
        {
            use crate::codegen::backend_trait::NativeBackend;
            use crate::codegen::llvm::LlvmBackend;

            let mut mir = mir;

            if !no_mangle {
                let prefix = module_prefix_from_path(file_path, source_root);
                let global_suffix_index = build_suffix_index(imports.all_mangled.as_ref());
                let unresolved = mangle_mir(
                    &mut mir,
                    &prefix,
                    is_entry,
                    imports.import_map.as_ref(),
                    imports.ambiguous_names.as_ref(),
                    &use_map,
                    &global_suffix_index,
                );
                if unresolved > 0 && std::env::var("SIMPLE_BOOTSTRAP").as_deref() != Ok("1") {
                    eprintln!(
                        "[llvm-entry-closure] {} unresolved call(s) in module `{}` before codegen; continuing so normal stub/link closure can resolve what bootstrap export discovery cannot",
                        unresolved,
                        module_prefix_from_path(file_path, source_root)
                    );
                }
            } else {
                if is_entry {
                    for func in &mut mir.functions {
                        if func.name == "main" {
                            func.name = "spl_main".to_string();
                        }
                    }
                }
            }

            let mut llvm =
                LlvmBackend::new(effective_target()).map_err(|e| format!("{}: llvm init: {e}", file_path.display()))?;
            llvm.set_import_map(imports.import_map.clone());
            llvm.set_use_map(use_map.clone());
            let obj = llvm
                .compile(&mir)
                .map_err(|e| format!("{}: llvm codegen: {e}", file_path.display()))?;

            if is_entry && std::env::var("SIMPLE_DEBUG_LLVM").is_ok() {
                if let Ok(ir) = llvm.get_ir() {
                    let ir_path = file_path.with_extension("ll");
                    let _ = std::fs::write(&ir_path, &ir);
                    eprintln!("[llvm] IR dumped to {}", ir_path.display());
                }
            }

            return Ok(obj);
        }
        #[cfg(not(feature = "llvm"))]
        return Err(format!(
            "{}: LLVM backend requested but 'llvm' feature not enabled",
            file_path.display()
        ));
    }

    // Cranelift backend (default)
    let mut codegen =
        Codegen::for_target(effective_target()).map_err(|e| format!("{}: codegen init: {e}", file_path.display()))?;
    codegen.set_entry_module(is_entry);
    codegen.set_import_map(imports.import_map.clone());
    codegen.set_ambiguous_names(imports.ambiguous_names.clone());
    codegen.set_use_map(use_map);
    codegen.set_data_exports(imports.data_exports.clone());
    if !no_mangle {
        let prefix = module_prefix_from_path(file_path, source_root);
        codegen.set_module_prefix(prefix);
    }
    let obj = codegen
        .compile_module(&mir)
        .map_err(|e| format!("{}: codegen: {e}", file_path.display()))?;

    Ok(obj)
}

/// Compile a file with panic catching and timeout.
#[allow(clippy::too_many_arguments)]
pub(crate) fn compile_file_safe(
    source: String,
    file_path: PathBuf,
    project_root: PathBuf,
    source_dirs: Vec<PathBuf>,
    fallback_root: PathBuf,
    timeout_secs: u64,
    stack_size: usize,
    no_mangle: bool,
    is_entry: bool,
    imports: ModuleImports,
) -> Result<Vec<u8>, String> {
    use std::sync::mpsc;

    let (tx, rx) = mpsc::channel();
    let handle = std::thread::Builder::new()
        .name(format!(
            "compile-{}",
            file_path.file_name().unwrap_or_default().to_string_lossy()
        ))
        .stack_size(stack_size)
        .spawn(move || {
            let source_root = source_root_for_file(&file_path, &source_dirs, &fallback_root);
            let result = if std::env::var("SIMPLE_NO_CATCH").is_ok() {
                compile_file_to_object(
                    &source,
                    &file_path,
                    &project_root,
                    &source_root,
                    &source_dirs,
                    no_mangle,
                    is_entry,
                    &imports,
                )
            } else {
                match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    compile_file_to_object(
                        &source,
                        &file_path,
                        &project_root,
                        &source_root,
                        &source_dirs,
                        no_mangle,
                        is_entry,
                        &imports,
                    )
                })) {
                    Ok(r) => r,
                    Err(e) => {
                        let msg = if let Some(s) = e.downcast_ref::<String>() {
                            format!("panic: {s}")
                        } else if let Some(s) = e.downcast_ref::<&str>() {
                            format!("panic: {s}")
                        } else {
                            "panic: unknown".to_string()
                        };
                        Err(msg)
                    }
                }
            };
            let _ = tx.send(());
            result
        })
        .map_err(|e| format!("spawn: {e}"))?;

    match rx.recv_timeout(Duration::from_secs(timeout_secs)) {
        Ok(()) => handle.join().unwrap_or_else(|_| Err("thread join error".to_string())),
        Err(_) => Err(format!("timeout ({}s)", timeout_secs)),
    }
}

/// Find the matching `>` for a string starting with `<...>`, handling nested `<>`.
fn find_balanced_gt(s: &str) -> Option<usize> {
    if !s.starts_with('<') {
        return None;
    }
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        if c == '<' {
            depth += 1;
        } else if c == '>' {
            depth -= 1;
            if depth == 0 {
                return Some(i);
            }
        }
    }
    None
}

/// Apply bootstrap source rewriting for the Rust seed compiler.
///
/// Handles: `?` stripping, `.?` -> `!= nil`, `fn()` types -> `any`,
/// `impl<>` stripping, `cli` block commenting, etc.
fn apply_bootstrap_rewrite(source: &str) -> String {
    // Protect ?? (null coalesce) before stripping ? from types
    let mut s = source.replace("??", "\x00COALESCE\x00");

    // Handle `.?` (optional chaining / nil-check) before general ? stripping.
    for pat in [".?:", ".?\n", ".?\r\n", ".? ", ".?\t", ".?)", ".?,", ".?]", ".?;"] {
        s = s.replace(pat, &format!(" != nil{}", &pat[2..]));
    }
    s = s.replace(".? =", " != nil =");
    if s.ends_with(".?") {
        let len = s.len();
        s.replace_range(len - 2.., " != nil");
    }

    // Strip `?` suffix from nullable types (Type? -> Type)
    for pat in ["? ", "?\n", "?\r\n", "?\t", "?,", "?)", "?]", "?>", "?:", "?=", "?;"] {
        while s.contains(pat) {
            s = s.replace(pat, &pat[1..]);
        }
    }
    if s.ends_with('?') {
        s.pop();
    }

    // Restore ?? (null coalesce) operator
    s = s.replace("\x00COALESCE\x00", "??");

    s = s.replace("/* complex expr */", "0");
    s = s.replace(" ~> ", " |> ");

    // Function-type parameters not yet supported in Rust parser.
    // Replace `fn(...)` type annotations with `any`.
    {
        let mut result = String::new();
        let bytes = s.as_bytes();
        let mut i = 0;
        let mut in_triple_quote = false;
        let mut in_single_quote = false;
        let mut in_comment = false;
        while i < bytes.len() {
            if !in_single_quote
                && !in_comment
                && i + 2 < bytes.len()
                && bytes[i] == b'"'
                && bytes[i + 1] == b'"'
                && bytes[i + 2] == b'"'
            {
                in_triple_quote = !in_triple_quote;
                result.push('"');
                result.push('"');
                result.push('"');
                i += 3;
                continue;
            }
            if in_triple_quote {
                result.push(bytes[i] as char);
                i += 1;
                continue;
            }
            if !in_comment && !in_single_quote && bytes[i] == b'"' {
                in_single_quote = true;
                result.push('"');
                i += 1;
                continue;
            }
            if in_single_quote {
                if bytes[i] == b'\\' && i + 1 < bytes.len() {
                    result.push(bytes[i] as char);
                    result.push(bytes[i + 1] as char);
                    i += 2;
                    continue;
                }
                if bytes[i] == b'"' {
                    in_single_quote = false;
                }
                result.push(bytes[i] as char);
                i += 1;
                continue;
            }
            if bytes[i] == b'#' {
                in_comment = true;
            }
            if in_comment {
                if bytes[i] == b'\n' {
                    in_comment = false;
                }
                result.push(bytes[i] as char);
                i += 1;
                continue;
            }
            let is_fn_type = i + 5 < bytes.len()
                && (bytes[i] == b':' || bytes[i] == b'=')
                && bytes[i + 1] == b' '
                && bytes[i + 2] == b'f'
                && bytes[i + 3] == b'n'
                && bytes[i + 4] == b'(';
            if !is_fn_type {
                result.push(bytes[i] as char);
                i += 1;
                continue;
            }
            result.push(bytes[i] as char);
            result.push(' ');
            let fn_start = i + 2;
            let mut depth = 0i32;
            let mut j = fn_start + 2;
            depth += 1;
            j += 1;
            while j < bytes.len() && depth > 0 {
                if bytes[j] == b'(' || bytes[j] == b'[' {
                    depth += 1;
                } else if bytes[j] == b')' || bytes[j] == b']' {
                    depth -= 1;
                }
                j += 1;
            }
            if j + 4 <= bytes.len() && &s[j..j + 4] == " -> " {
                j += 4;
                let mut type_depth = 0i32;
                while j < bytes.len() {
                    let c = bytes[j];
                    if c == b'<' || c == b'(' || c == b'[' {
                        type_depth += 1;
                    } else if c == b'>' || c == b')' || c == b']' {
                        if type_depth > 0 {
                            type_depth -= 1;
                        } else {
                            break;
                        }
                    } else if type_depth == 0
                        && (c == b',' || c == b':' || c == b'\n' || c == b'\r' || c == b'#' || c == b' ')
                    {
                        break;
                    }
                    j += 1;
                }
            }
            if j < bytes.len() && bytes[j] == b':' {
                result.push_str("fn()");
            } else {
                result.push_str("any");
            }
            i = j;
        }
        s = result;
    }
    // Bare `fn` as field type
    s = s.replace(": fn\n", ": any\n");
    s = s.replace(": fn\r\n", ": any\r\n");

    // `cli Name:` blocks are not supported -- comment out the entire block
    {
        let mut result = String::new();
        let mut in_cli_block = false;
        let mut cli_indent: Option<usize> = None;
        for line in s.lines() {
            let trimmed = line.trim_start();
            if trimmed.starts_with("cli ") && trimmed.contains(':') && !trimmed.starts_with('#') {
                in_cli_block = true;
                cli_indent = Some(line.len() - trimmed.len());
                result.push_str("# ");
                result.push_str(line);
                result.push('\n');
                continue;
            }
            if in_cli_block {
                let line_indent = line.len() - line.trim_start().len();
                if trimmed.is_empty() || line_indent > cli_indent.unwrap_or(0) {
                    result.push_str("# ");
                    result.push_str(line);
                    result.push('\n');
                    continue;
                } else {
                    in_cli_block = false;
                    cli_indent = None;
                }
            }
            result.push_str(line);
            result.push('\n');
        }
        if !s.ends_with('\n') && result.ends_with('\n') {
            result.pop();
        }
        s = result;
    }

    // Generic impl blocks: `impl<T, E> Type<T, E>:` -> `impl Type:`
    {
        let mut result = String::new();
        for line in s.lines() {
            let trimmed = line.trim_start();
            if trimmed.starts_with("impl<") {
                let indent = &line[..line.len() - trimmed.len()];
                let rest = &trimmed[4..];
                let after_generic = if let Some(gt) = find_balanced_gt(rest) {
                    &rest[gt + 1..]
                } else {
                    rest
                };
                let after_generic = after_generic.trim_start();
                let clean_type = if let Some(lt_pos) = after_generic.find('<') {
                    if let Some(rest_after) = after_generic.get(lt_pos..) {
                        if let Some(gt) = find_balanced_gt(rest_after) {
                            format!("{}{}", &after_generic[..lt_pos], &rest_after[gt + 1..])
                        } else {
                            after_generic.to_string()
                        }
                    } else {
                        after_generic.to_string()
                    }
                } else {
                    after_generic.to_string()
                };
                let clean_type = if let Some(w) = clean_type.find(" where ") {
                    format!("{}:", &clean_type[..w])
                } else {
                    clean_type
                };
                result.push_str(indent);
                result.push_str("impl ");
                result.push_str(&clean_type);
                result.push('\n');
            } else {
                result.push_str(line);
                result.push('\n');
            }
        }
        if !s.ends_with('\n') && result.ends_with('\n') {
            result.pop();
        }
        s = result;
    }

    s
}
