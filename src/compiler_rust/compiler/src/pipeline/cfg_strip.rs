//! Shared `@cfg(<arch>)` function-variant filtering.
//!
//! Same-named per-arch `@cfg` variants (e.g. six `fn foo` bodies, one per
//! `@cfg(x86_64)`/`@cfg(riscv64)`/...) otherwise all survive into one
//! compilation unit / interpreter registry, where first-wins registration
//! (codegen `declare_functions`, interpreter `functions.insert`) picks
//! whichever is declared FIRST in source order -- not target-aware -- so every
//! target whose variant is not written first is mis-dispatched to a wrong-arch
//! body (bug `x64_freestanding_cfg_multivariant_misdispatch`).
//!
//! This module hosts the strip logic shared by ALL execution paths:
//!   * native_project builds (`pipeline/native_project/compiler.rs`,
//!     `imports.rs`) -- strip against the build's effective target arch;
//!   * `bin/simple run` JIT + interpreter paths (driver `exec_core.rs`) and
//!     interpreter module registration (`interpreter_eval.rs`,
//!     `interpreter_module/module_loader.rs`) -- strip against the HOST arch,
//!     since interpreted/JIT code always executes on the host.
//!
//! Post-strip semantics:
//!   * exactly one survivor -> it binds;
//!   * >= 2 same-name survivors that are each active `@cfg(<arch>)` variants
//!     with the same arity -> duplicate-definition diagnostic (warning for
//!     now: code relying on first-wins ordering must not hard-break);
//!   * zero survivors -> the name is recorded so the call site can report
//!     "no active @cfg variant for <arch>" instead of silently executing a
//!     wrong-arch body.
//!
//! Only recognized arch aliases (and `not(<arch>)`) gate; `test`, `baremetal`,
//! `("key", "value")` cfgs, etc. are left untouched, matching the pure-Simple
//! preprocessor (`parser_preprocessor.spl` `_pp_cfg_condition_matches`).

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use simple_common::target::{Target, TargetArch, TargetOS};
use simple_parser::ast::{Attribute, Node};

/// Apply module-level `@when`/`@elif`/`@else`/`@end` selection for `target`
/// (OS and arch) before the Rust seed parses imports. Delegates to the
/// parser's single owner (`simple_parser::cond_compile`) so this path accepts
/// exactly what the lexer accepts. Inactive and directive lines are blanked,
/// kept lines stay verbatim, line numbers are preserved. Unknown atoms
/// evaluate false and are reported as warnings (as the parser does for the
/// lexer path); unbalanced directives fail closed instead of compiling both
/// branches.
pub(crate) fn strip_os_when_blocks(source: &str, target: Target) -> Result<String, String> {
    let (selected, diagnostics) =
        simple_parser::cond_compile::select_branches(source, target.os.name(), target.arch.name());
    if let Some(error) = diagnostics
        .iter()
        .find(|d| d.contains("without @when") || d.contains("unclosed"))
    {
        return Err(error.clone());
    }
    for diagnostic in &diagnostics {
        eprintln!("warning: conditional compilation ({}/{}): {diagnostic}", target.os.name(), target.arch.name());
    }
    Ok(selected)
}

/// Resolve a `@cfg(...)` condition name to an architecture, if it names one.
///
/// Mirrors the arch-alias groups in the pure-Simple preprocessor
/// (`src/compiler/10.frontend/core/parser_preprocessor.spl`
/// `_pp_cfg_condition_matches`) so an arch gate is recognized the same way
/// here as it is by the self-hosted compiler's own `@cfg` evaluation. Returns
/// `None` for condition names that are not arch aliases (e.g. `test`,
/// `baremetal`, a bare `not(...)` on a non-arch name, or a `"key", "value"`
/// pair) -- those are intentionally left ungated rather than risk excluding a
/// declaration that should build.
pub(crate) fn cfg_name_to_arch(name: &str) -> Option<TargetArch> {
    match name {
        "x86_64" | "amd64" | "x64" => Some(TargetArch::X86_64),
        "x86" | "i386" | "i686" => Some(TargetArch::X86),
        "aarch64" | "arm64" => Some(TargetArch::Aarch64),
        "arm" | "armv7" | "armv6" | "arm32" => Some(TargetArch::Arm),
        "riscv64" => Some(TargetArch::Riscv64),
        "riscv32" => Some(TargetArch::Riscv32),
        _ => None,
    }
}

fn cfg_line_arch_verdict(line: &str, target_arch: TargetArch) -> Option<bool> {
    let condition = line.trim().strip_prefix("@cfg(")?.strip_suffix(')')?.trim();
    let (name, negate) = condition
        .strip_prefix("not(")
        .and_then(|inner| inner.strip_suffix(')'))
        .map_or((condition, false), |name| (name.trim(), true));
    cfg_name_to_arch(name).map(|arch| (arch == target_arch) != negate)
}

fn is_top_level_global_decl(line: &str) -> bool {
    if line.trim_start() != line {
        return false;
    }
    let mut declaration = line.trim();
    if let Some(rest) = declaration.strip_prefix("pub ") {
        declaration = rest;
    } else if let Some(rest) = declaration.strip_prefix("pub(") {
        let close = rest.find(')');
        if let Some(close) = close {
            declaration = rest[close + 1..].trim_start();
        }
    }
    if declaration.starts_with("static fn ") || declaration.starts_with("static me ") {
        return false;
    }
    ["let ", "val ", "var ", "const ", "static "]
        .iter()
        .any(|prefix| declaration.starts_with(prefix))
}

fn delimiter_delta(line: &str, triple_quote: &mut Option<u8>) -> i64 {
    let bytes = line.as_bytes();
    let mut delta = 0;
    let mut index = 0;
    while index < bytes.len() {
        if let Some(quote) = *triple_quote {
            if index + 2 < bytes.len()
                && bytes[index] == quote
                && bytes[index + 1] == quote
                && bytes[index + 2] == quote
            {
                *triple_quote = None;
                index += 3;
            } else {
                index += 1;
            }
            continue;
        }

        let byte = bytes[index];
        if (byte == b'\'' || byte == b'"')
            && index + 2 < bytes.len()
            && bytes[index + 1] == byte
            && bytes[index + 2] == byte
        {
            *triple_quote = Some(byte);
            index += 3;
            continue;
        }
        if byte == b'\'' || byte == b'"' {
            let quote = byte;
            index += 1;
            while index < bytes.len() {
                if bytes[index] == b'\\' {
                    index += 2;
                } else if bytes[index] == quote {
                    index += 1;
                    break;
                } else {
                    index += 1;
                }
            }
            continue;
        }
        match byte {
            b'#' => break,
            b'(' | b'[' | b'{' => delta += 1,
            b')' | b']' | b'}' => delta -= 1,
            _ => {}
        }
        index += 1;
    }
    delta
}

fn global_decl_end(lines: &[&str], start: usize) -> usize {
    let mut end = start;
    let mut triple_quote = None;
    let mut depth = delimiter_delta(lines[start], &mut triple_quote).max(0);
    while end + 1 < lines.len() {
        let next = lines[end + 1];
        let continuation = triple_quote.is_some() || depth > 0 || next.trim().is_empty() || next.trim_start() != next;
        if !continuation {
            break;
        }
        end += 1;
        depth = (depth + delimiter_delta(lines[end], &mut triple_quote)).max(0);
    }
    end
}

fn doc_comment_end(lines: &[&str], start: usize) -> Option<usize> {
    let trimmed = lines[start].trim();
    if trimmed.starts_with("///") {
        if trimmed != "///" {
            return Some(start + 1);
        }
        return (start + 1..lines.len())
            .find(|index| lines[*index].trim() == "///")
            .map(|end| end + 1);
    }
    if trimmed.starts_with("/**") {
        if trimmed[3..].contains("*/") {
            return Some(start + 1);
        }
        return (start + 1..lines.len())
            .find(|index| lines[*index].contains("*/"))
            .map(|end| end + 1);
    }
    for delimiter in ["\"\"\"", "'''"] {
        if let Some(rest) = trimmed.strip_prefix(delimiter) {
            if rest.contains(delimiter) {
                return Some(start + 1);
            }
            return (start + 1..lines.len())
                .find(|index| lines[*index].contains(delimiter))
                .map(|end| end + 1);
        }
    }
    None
}

/// Blank inactive top-level global variants before parsing.
///
/// The seed AST retains attributes on functions but discards them on globals,
/// so globals must be selected while the source still carries its `@cfg`.
/// Blank replacement preserves source line numbers for diagnostics.
pub fn strip_inactive_cfg_arch_globals(source: &str, target_arch: TargetArch) -> String {
    // Host-arch callers are the interpreter/JIT `run` paths, which never pass
    // through native discovery's OS-branch preprocessing. Without this, any
    // module carrying an `@when(os="windows"): ... @else: ... @end` block
    // (e.g. std io/windows_redirected_process.spl, reached from io_runtime)
    // fails to parse under `simple run`. A malformed block is left untouched so
    // the parser still rejects it (fail closed, never both branches).
    let os_selected;
    let source = if target_arch == TargetArch::host() {
        match strip_os_when_blocks(source, Target::new(target_arch, TargetOS::host())) {
            Ok(selected) => {
                os_selected = selected;
                os_selected.as_str()
            }
            Err(_) => source,
        }
    } else {
        source
    };
    let lines: Vec<&str> = source.split('\n').collect();
    let mut filtered = Vec::with_capacity(lines.len());
    let mut index = 0;
    while index < lines.len() {
        if lines[index].trim_start() == lines[index] && lines[index].trim().starts_with('@') {
            let group_start = index;
            let mut declaration = index;
            let mut cfg_lines = Vec::new();
            while declaration < lines.len() {
                let line = lines[declaration];
                let trimmed = line.trim();
                if line.trim_start() == line && trimmed.starts_with('@') {
                    if let Some(active) = cfg_line_arch_verdict(line, target_arch) {
                        cfg_lines.push((declaration, active));
                    }
                    declaration += 1;
                } else if let Some(after_doc) = doc_comment_end(&lines, declaration) {
                    declaration = after_doc;
                } else if trimmed.is_empty() || trimmed.starts_with('#') {
                    declaration += 1;
                } else {
                    break;
                }
            }
            if !cfg_lines.is_empty() && declaration < lines.len() && is_top_level_global_decl(lines[declaration]) {
                if cfg_lines.iter().any(|(_, active)| !active) {
                    let end = global_decl_end(&lines, declaration);
                    filtered.extend((group_start..=end).map(|_| ""));
                    index = end + 1;
                    continue;
                }
                for (line_index, line) in lines[group_start..declaration].iter().enumerate() {
                    let absolute_index = group_start + line_index;
                    if cfg_lines.iter().any(|(cfg_index, _)| *cfg_index == absolute_index) {
                        filtered.push("");
                    } else {
                        filtered.push(*line);
                    }
                }
                index = declaration;
                continue;
            }
        }
        filtered.push(lines[index]);
        index += 1;
    }
    filtered.join("\n")
}

pub(crate) fn parse_cfg_filtered_module(
    source: &str,
    target_arch: TargetArch,
) -> Result<simple_parser::ast::Module, String> {
    let filtered = strip_inactive_cfg_arch_globals(source, target_arch);
    let mut module = simple_parser::Parser::new(&filtered)
        .parse()
        .map_err(|error| error.to_string())?;
    strip_inactive_cfg_arch_fns(&mut module, target_arch);
    Ok(module)
}

/// Evaluate a single `@cfg(...)` attribute's architecture verdict for
/// `target_arch`. Returns:
///   * `Some(true)`  -- this `@cfg` names an arch that matches the target,
///   * `Some(false)` -- this `@cfg` names an arch that does NOT match,
///   * `None`        -- not a bare arch alias (`test`, `baremetal`,
///                      `("target_arch", "arm")`, empty `@cfg()`, etc.) --
///                      leave ungated.
pub(crate) fn cfg_attr_arch_verdict(attr: &Attribute, target_arch: TargetArch) -> Option<bool> {
    use simple_parser::ast::Expr;
    let args = attr.args.as_ref()?;
    // Only a single bare condition is an arch gate; `("key", "value")` string
    // pairs and an empty `@cfg()` are not.
    if args.len() != 1 {
        return None;
    }
    match &args[0] {
        // `@cfg(not(<arch>))`
        Expr::Call {
            callee,
            args: call_args,
        } => {
            if let Expr::Identifier(fname) = callee.as_ref() {
                if fname == "not" && call_args.len() == 1 {
                    if let Expr::Identifier(name) = &call_args[0].value {
                        return cfg_name_to_arch(name).map(|arch| arch != target_arch);
                    }
                }
            }
            None
        }
        // `@cfg(<arch>)`
        Expr::Identifier(name) => cfg_name_to_arch(name).map(|arch| arch == target_arch),
        _ => None,
    }
}

/// True if any `@cfg` attribute names an arch that does NOT match `arch`
/// (i.e. this declaration is an inactive variant and must not execute).
pub fn fn_inactive_cfg_arch(attrs: &[Attribute], arch: TargetArch) -> bool {
    attrs
        .iter()
        .any(|a| a.name == "cfg" && cfg_attr_arch_verdict(a, arch) == Some(false))
}

/// True if any `@cfg` attribute names an arch that matches `arch`
/// (i.e. this declaration is an explicitly arch-gated ACTIVE variant).
pub fn fn_active_cfg_arch(attrs: &[Attribute], arch: TargetArch) -> bool {
    attrs
        .iter()
        .any(|a| a.name == "cfg" && cfg_attr_arch_verdict(a, arch) == Some(true))
}

/// [`fn_inactive_cfg_arch`] against the host architecture (the arch that
/// interpreted / JIT-executed code actually runs on).
pub fn fn_inactive_cfg_arch_for_host(attrs: &[Attribute]) -> bool {
    fn_inactive_cfg_arch(attrs, TargetArch::host())
}

/// [`fn_active_cfg_arch`] against the host architecture.
pub fn fn_active_cfg_arch_for_host(attrs: &[Attribute]) -> bool {
    fn_active_cfg_arch(attrs, TargetArch::host())
}

thread_local! {
    /// Function names whose `@cfg(<arch>)` variants were stripped on this
    /// thread. Consulted by the interpreter's undefined-function error path so
    /// "all variants stripped" reports "no active @cfg variant for <arch>"
    /// instead of a generic not-found (and NEVER silently runs a wrong body).
    static STRIPPED_FNS: RefCell<HashSet<String>> = RefCell::new(HashSet::new());
}

/// Record that a `@cfg`-inactive variant of `name` was dropped.
pub fn note_stripped_fn(name: &str) {
    STRIPPED_FNS.with(|cell| {
        cell.borrow_mut().insert(name.to_string());
    });
}

/// If every variant of `name` was `@cfg`-stripped, a help string explaining
/// why the function is undefined on this target.
pub fn stripped_fn_hint(name: &str) -> Option<String> {
    let stripped = STRIPPED_FNS.with(|cell| cell.borrow().contains(name));
    if stripped {
        Some(format!(
            "no active @cfg variant of `{}` for target arch `{}` -- every definition is \
             gated on a different architecture",
            name,
            TargetArch::host().name()
        ))
    } else {
        None
    }
}

/// Warn (once per name) about >= 2 surviving same-name, same-arity functions
/// that are each ACTIVE `@cfg(<arch>)` variants: a duplicate definition that
/// first-wins registration would silently collapse. Kept as a warning (not an
/// error) for now -- see module docs on blast radius.
fn warn_duplicate_active_variants(items: &[Node], arch: TargetArch) {
    let mut seen: HashMap<(String, usize), usize> = HashMap::new();
    for item in items {
        if let Node::Function(f) = item {
            if fn_active_cfg_arch(&f.attributes, arch) {
                *seen.entry((f.name.clone(), f.params.len())).or_insert(0) += 1;
            }
        }
    }
    for ((name, _arity), count) in seen {
        if count > 1 {
            eprintln!(
                "warning: duplicate active @cfg variants of `{}` for target arch `{}` \
                 ({} definitions match); the first definition wins -- remove or re-gate \
                 the duplicates",
                name,
                arch.name(),
                count
            );
        }
    }
}

/// Drop top-level `@cfg(<arch>)`-gated function nodes whose architecture does
/// not match `target_arch`, recording stripped names and warning about
/// duplicate active variants. Item-list form shared by module- and
/// interpreter-level callers.
pub fn strip_inactive_cfg_arch_fn_nodes(items: &mut Vec<Node>, target_arch: TargetArch) {
    items.retain(|item| {
        if let Node::Function(f) = item {
            if fn_inactive_cfg_arch(&f.attributes, target_arch) {
                note_stripped_fn(&f.name);
                return false;
            }
        }
        true
    });
    warn_duplicate_active_variants(items, target_arch);
}

/// Drop top-level `@cfg(<arch>)`-gated function definitions whose architecture
/// does not match `target_arch`. See module docs for why (multivariant
/// misdispatch) and the exact gating rules.
pub fn strip_inactive_cfg_arch_fns(module: &mut simple_parser::ast::Module, target_arch: TargetArch) {
    strip_inactive_cfg_arch_fn_nodes(&mut module.items, target_arch);
}

/// [`strip_inactive_cfg_arch_fns`] against the host architecture -- the strip
/// every `bin/simple run` execution path (JIT and interpreter) must apply
/// post-parse.
pub fn strip_inactive_cfg_arch_fns_for_host(module: &mut simple_parser::ast::Module) {
    strip_inactive_cfg_arch_fns(module, TargetArch::host());
}

#[cfg(test)]
mod tests {
    use super::*;

    fn linux_host() -> Target {
        Target::new(TargetArch::host(), TargetOS::Linux)
    }

    #[test]
    fn host_globals_strip_selects_host_os_when_branch_for_run_paths() {
        // `simple run` / interpreter module loading reach this function with the
        // HOST arch and never pass through native discovery's OS preprocessing.
        let source = "@when(os=\"windows\"):\nfn pick() -> i64:\n    11\n@else:\nfn pick() -> i64:\n    22\n@end\n";
        let filtered = strip_inactive_cfg_arch_globals(source, TargetArch::host());
        assert_eq!(filtered.lines().count(), source.lines().count());
        assert!(!filtered.contains("@when") && !filtered.contains("@else") && !filtered.contains("@end"));
        let (kept, dropped) = if TargetOS::host() == TargetOS::Windows { ("11", "22") } else { ("22", "11") };
        assert!(filtered.contains(kept) && !filtered.contains(dropped));
        assert!(simple_parser::Parser::new(&filtered).parse().is_ok());
        // Unknown atoms evaluate false (same as the lexer): the branch is dropped.
        let unknown = "@when(os=\"unknown\"):\nval A = 1\n@end\n";
        assert_eq!(strip_inactive_cfg_arch_globals(unknown, TargetArch::host()), "\n\n\n");
        // Unbalanced blocks are left untouched so the parser still rejects them.
        let malformed = "@when(os=\"windows\"):\nval A = 1\n";
        assert_eq!(strip_inactive_cfg_arch_globals(malformed, TargetArch::host()), malformed);
    }

    #[test]
    fn os_when_path_identity_selects_nested_platform_owner() {
        let source = include_str!("../../../../lib/nogc_sync_mut/io/path_identity_abi.spl");
        // The POSIX errno owner lives in `_PathIdentityPosix/errno_abi.spl` and is
        // imported only by the non-Windows branch.
        let posix_errno = "use std.nogc_sync_mut.io._PathIdentityPosix.errno_abi.{path_errno_address}";
        for (os, expected, excluded) in [
            (TargetOS::Linux, posix_errno, "fn path_errno_address() -> i64: 0"),
            (TargetOS::FreeBSD, posix_errno, "fn path_errno_address() -> i64: 0"),
            (TargetOS::MacOS, posix_errno, "fn path_errno_address() -> i64: 0"),
            (TargetOS::Windows, "fn path_errno_address() -> i64: 0", posix_errno),
        ] {
            let filtered = super::strip_os_when_blocks(source, Target::new(TargetArch::host(), os)).expect("platform owner branch");
            assert_eq!(filtered.lines().count(), source.lines().count());
            assert!(filtered.contains(expected), "{os:?}");
            assert!(!filtered.contains(excluded), "{os:?}");
            assert!(simple_parser::Parser::new(&filtered).parse().is_ok(), "{os:?}");
        }
    }

    #[test]
    fn os_when_blocks_select_one_parseable_branch_and_keep_line_numbers() {
        let source = "val TOKEN = 7\n@when(os=\"windows\"):\nuse std.io_runtime.{thread_sleep}\nfn selected() -> i64:\n    11\n@else:\nfn selected() -> i64:\n    22\n@end\nexport TOKEN, selected\n";
        for (os, expected, excluded) in [
            (TargetOS::Windows, "    11", "    22"),
            (TargetOS::Linux, "    22", "    11"),
        ] {
            let filtered = super::strip_os_when_blocks(source, Target::new(TargetArch::host(), os)).expect("supported OS block");
            assert_eq!(filtered.lines().count(), source.lines().count());
            assert!(filtered.contains(expected));
            assert!(!filtered.contains(excluded));
            assert!(simple_parser::Parser::new(&filtered).parse().is_ok());
        }
        // Unknown atoms evaluate false, like the lexer: the block is dropped.
        let unknown = super::strip_os_when_blocks("@when(os=\"unknown\"):\nfn u() -> i64: 1\n@end\n", Target::new(TargetArch::host(), TargetOS::Linux))
            .expect("unknown atom is false, not an error");
        assert!(!unknown.contains("fn u"));
        // @elif selects the first matching branch (previously rejected).
        let elif = "@when(os=\"windows\"):\nfn e() -> i64: 1\n@elif(os=\"linux\"):\nfn e() -> i64: 2\n@else:\nfn e() -> i64: 3\n@end\n";
        let linux = super::strip_os_when_blocks(elif, linux_host()).expect("elif block");
        assert!(linux.contains("fn e() -> i64: 2") && !linux.contains(": 1") && !linux.contains(": 3"));
        assert_eq!(linux.lines().count(), elif.lines().count());
        // Unbalanced structure still fails closed.
        assert!(super::strip_os_when_blocks("@else:\n", linux_host()).is_err());
        assert!(super::strip_os_when_blocks("@end\n", linux_host()).is_err());
        assert!(super::strip_os_when_blocks("@when(os=\"windows\"):\n", linux_host()).is_err());
        assert!(super::strip_os_when_blocks("@elif(os=\"windows\"):\n", linux_host()).is_err());
        let nested = "@when(os=\"windows\"):\n@when(os=\"windows\"):\nval SELECTED = 11\n@else:\nval SELECTED = 22\n@end\n@else:\nval SELECTED = 33\n@end\n";
        let windows = super::strip_os_when_blocks(nested, Target::new(TargetArch::host(), TargetOS::Windows)).expect("nested Windows branch");
        let linux = super::strip_os_when_blocks(nested, linux_host()).expect("nested Linux fallback");
        assert!(windows.contains("val SELECTED = 11"));
        assert!(!windows.contains("val SELECTED = 22"));
        assert!(linux.contains("val SELECTED = 33"));
        assert!(!linux.contains("val SELECTED = 11"));
        assert!(simple_parser::Parser::new(&windows).parse().is_ok());
        assert!(simple_parser::Parser::new(&linux).parse().is_ok());
    }
    #[test]
    fn cfg_globals_select_aarch64_and_riscv64_before_hir_lowering() {
        let source = "\
@cfg(riscv64)\nval LET_R_FIRST = 11\n@cfg(aarch64)\nval LET_R_FIRST = 12\n\
@cfg(aarch64)\nval LET_A_FIRST = 21\n@cfg(riscv64)\nval LET_A_FIRST = 22\n\
@cfg(riscv64)\nconst CONST_R_FIRST = 31\n@cfg(aarch64)\nconst CONST_R_FIRST = 32\n\
@cfg(aarch64)\nconst CONST_A_FIRST = 41\n@cfg(riscv64)\nconst CONST_A_FIRST = 42\n\
@cfg(riscv64)\nstatic STATIC_R_FIRST = 51\n@cfg(aarch64)\nstatic STATIC_R_FIRST = 52\n\
@cfg(aarch64)\nstatic STATIC_A_FIRST = 61\n@cfg(riscv64)\nstatic STATIC_A_FIRST = 62\n";

        let selected_values = |arch| {
            let filtered = strip_inactive_cfg_arch_globals(source, arch);
            let module = simple_parser::Parser::new(&filtered)
                .parse()
                .expect("parse cfg globals");
            crate::hir::lower_with_context_lenient(&module, std::path::Path::new("cfg_globals.spl"))
                .expect("lower cfg globals")
                .global_init_values
        };

        let aarch64 = selected_values(TargetArch::Aarch64);
        assert_eq!(aarch64.get("LET_R_FIRST"), Some(&12));
        assert_eq!(aarch64.get("LET_A_FIRST"), Some(&21));
        assert_eq!(aarch64.get("CONST_R_FIRST"), Some(&32));
        assert_eq!(aarch64.get("CONST_A_FIRST"), Some(&41));
        assert_eq!(aarch64.get("STATIC_R_FIRST"), Some(&52));
        assert_eq!(aarch64.get("STATIC_A_FIRST"), Some(&61));

        let riscv64 = selected_values(TargetArch::Riscv64);
        assert_eq!(riscv64.get("LET_R_FIRST"), Some(&11));
        assert_eq!(riscv64.get("LET_A_FIRST"), Some(&22));
        assert_eq!(riscv64.get("CONST_R_FIRST"), Some(&31));
        assert_eq!(riscv64.get("CONST_A_FIRST"), Some(&42));
        assert_eq!(riscv64.get("STATIC_R_FIRST"), Some(&51));
        assert_eq!(riscv64.get("STATIC_A_FIRST"), Some(&62));
    }

    #[test]
    fn cfg_globals_cover_visibility_docs_and_column_zero_triple_close() {
        let source = r#"@align(8)
@cfg(riscv64)
/// RISC-V value
"""RISC-V extra documentation"""
pub(peer) val DOC_VALUE = """riscv64
payload
"""
@align(8)
@cfg(aarch64)
/**
 * AArch64 value
 */
"""AArch64 extra documentation"""
pub(up) val DOC_VALUE = """aarch64
payload
"""
"#;

        let selected = |arch| {
            let filtered = strip_inactive_cfg_arch_globals(source, arch);
            assert_eq!(filtered.split('\n').count(), source.split('\n').count());
            let module = parse_cfg_filtered_module(&filtered, arch).expect("parse selected documented global");
            crate::hir::lower_with_context_lenient(&module, std::path::Path::new("cfg_doc_globals.spl"))
                .expect("lower selected documented global")
                .global_init_strings
                .remove("DOC_VALUE")
                .expect("selected DOC_VALUE initializer")
        };

        let aarch64 = selected(TargetArch::Aarch64);
        assert!(aarch64.contains("aarch64"));
        assert!(!aarch64.contains("riscv64"));

        let riscv64 = selected(TargetArch::Riscv64);
        assert!(riscv64.contains("riscv64"));
        assert!(!riscv64.contains("aarch64"));
    }
}
