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

use simple_common::target::TargetArch;
pub use simple_parser::cond_compile::CfgTarget;
use simple_parser::ast::{Attribute, Node};

/// The conditional-compilation target of this process -- exactly what the
/// lexer evaluates against (`simple_parser::cond_compile::default_target`:
/// explicit `--target` > `SIMPLE_NATIVE_BUILD_TARGET` > `SIMPLE_TARGET_OS`/
/// `SIMPLE_TARGET_ARCH` > host). Every text-level strip caller (discovery,
/// import loader, parsed-source cache, `simple run`) uses these names, so it
/// can never disagree with the lexer path.
pub fn cfg_target() -> CfgTarget {
    CfgTarget::from_env()
}

/// Apply module-level `@when`/`@elif`/`@else`/`@end` selection for `target`
/// before the Rust seed parses imports. Delegates to the parser's single
/// owner (`simple_parser::cond_compile`) so this path accepts exactly what
/// the lexer accepts. Inactive and directive lines are blanked, kept lines
/// stay verbatim, line numbers are preserved. Unknown atoms evaluate false
/// and are reported as warnings (as the parser does for the lexer path);
/// unbalanced directives fail closed instead of compiling both branches.
pub(crate) fn strip_os_when_blocks(source: &str, target: &CfgTarget) -> Result<String, String> {
    let selection = simple_parser::cond_compile::select_branches(source, &target.os, &target.arch);
    if !selection.balanced {
        return Err(selection.diagnostics.join("; "));
    }
    for diagnostic in &selection.diagnostics {
        let line = format!("warning: conditional compilation ({}/{}): {diagnostic}", target.os, target.arch);
        // One file is reached by several lanes (discovery, siblings, import
        // loader, parsed-source cache): print each distinct warning once.
        let first_time = WARNED.with(|cell| cell.borrow_mut().insert(line.clone()));
        if first_time {
            eprintln!("{line}");
        }
    }
    Ok(selection.source)
}

thread_local! {
    /// Conditional-compilation warnings already printed on this thread.
    static WARNED: RefCell<HashSet<String>> = RefCell::new(HashSet::new());
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
    let trimmed = line.trim();
    let condition = trimmed.strip_prefix("@cfg(")?.strip_suffix(')')?.trim();
    if condition.is_empty() {
        return None;
    }
    if let Some(arch) = cfg_name_to_arch(condition) {
        return Some(arch == target_arch);
    }
    if let Some(inner) = condition.strip_prefix("not(").and_then(|s| s.strip_suffix(')')) {
        if let Some(arch) = cfg_name_to_arch(inner.trim()) {
            return Some(arch != target_arch);
        }
    }
    let snippet = format!("{trimmed}\nfn __cfg_probe():\n    0\n");
    let module = simple_parser::Parser::new(&snippet).parse().ok()?;
    let simple_parser::ast::Node::Function(func) = module.items.first()? else {
        return None;
    };
    let attr = func.attributes.first()?;
    if attr.name != "cfg" {
        return None;
    }
    cfg_attr_arch_verdict(attr, target_arch)
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
        || is_top_level_import_decl(declaration)
}

/// Top-level module edges (`use`, `import`, `from m import`, `common use`,
/// `export ... from m`). Blanking an inactive `@cfg(arch)` import here keeps
/// the other-arch module out of dependency collection, matching the
/// pure-Simple preprocessor, which blanks whatever declaration follows a false
/// `@cfg` (seed_cfg_on_top_level_use_ignored_2026-11-21).
fn is_top_level_import_decl(declaration: &str) -> bool {
    // `use =` / `export.x` are expressions (soft keywords): require an
    // identifier-ish start after the keyword.
    let starts_ident = |rest: &str| rest.trim_start().chars().next().is_some_and(|c| c.is_alphabetic() || c == '_' || c == '{' || c == '*');
    for keyword in ["use ", "import ", "from ", "common use "] {
        if let Some(rest) = declaration.strip_prefix(keyword) {
            return starts_ident(rest);
        }
    }
    declaration
        .strip_prefix("export ")
        .is_some_and(|rest| starts_ident(rest) && rest.contains(" from "))
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
        match strip_os_when_blocks(source, &cfg_target()) {
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

/// Recursively evaluate an architecture `@cfg(...)` expression tree
/// (`<arch>`, `not(...)` / `!`, `or` / `||`, `and` / `&&`, `all(...)`, `any(...)`).
///
/// Mirrors `src/compiler/50.mir/mir_cfg_select.spl`: if ANY sub-term is not a
/// recognized architecture alias (e.g. `test`, `baremetal`, `"key", "value"`),
/// returns `None` without short-circuiting so mixed non-arch gates stay ungated.
pub(crate) fn cfg_compound_arch_verdict(
    expr: &simple_parser::ast::Expr,
    target_arch: TargetArch,
) -> Option<bool> {
    use simple_parser::ast::{BinOp, Expr, UnaryOp};
    match expr {
        Expr::Identifier(name) => cfg_name_to_arch(name).map(|arch| arch == target_arch),
        Expr::Unary {
            op: UnaryOp::Not,
            operand,
        } => cfg_compound_arch_verdict(operand, target_arch).map(|v| !v),
        Expr::Binary {
            op: BinOp::Or,
            left,
            right,
        } => {
            let l = cfg_compound_arch_verdict(left, target_arch)?;
            let r = cfg_compound_arch_verdict(right, target_arch)?;
            Some(l || r)
        }
        Expr::Binary {
            op: BinOp::And,
            left,
            right,
        } => {
            let l = cfg_compound_arch_verdict(left, target_arch)?;
            let r = cfg_compound_arch_verdict(right, target_arch)?;
            Some(l && r)
        }
        Expr::Call {
            callee,
            args: call_args,
        } => {
            let Expr::Identifier(fname) = callee.as_ref() else {
                return None;
            };
            if call_args.iter().any(|arg| arg.name.is_some()) {
                return None;
            }
            match fname.as_str() {
                "not" if call_args.len() == 1 => {
                    cfg_compound_arch_verdict(&call_args[0].value, target_arch).map(|v| !v)
                }
                "all" | "and" if !call_args.is_empty() => {
                    let mut all_true = true;
                    for arg in call_args {
                        let v = cfg_compound_arch_verdict(&arg.value, target_arch)?;
                        all_true &= v;
                    }
                    Some(all_true)
                }
                "any" | "or" if !call_args.is_empty() => {
                    let mut any_true = false;
                    for arg in call_args {
                        let v = cfg_compound_arch_verdict(&arg.value, target_arch)?;
                        any_true |= v;
                    }
                    Some(any_true)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Evaluate a single `@cfg(...)` attribute's architecture verdict for
/// `target_arch`. Returns:
///   * `Some(true)`  -- this `@cfg` names an arch expression that matches the target,
///   * `Some(false)` -- this `@cfg` names an arch expression that does NOT match,
///   * `None`        -- not a pure arch expression (`test`, `baremetal`,
///                      `("target_arch", "arm")`, empty `@cfg()`, etc.) --
///                      leave ungated.
pub(crate) fn cfg_attr_arch_verdict(attr: &Attribute, target_arch: TargetArch) -> Option<bool> {
    if attr.named_args.is_some() {
        return None;
    }
    let args = attr.args.as_ref()?;
    // Only a single condition expression is an arch gate; `("key", "value")`
    // string pairs and an empty `@cfg()` are not.
    if args.len() != 1 {
        return None;
    }
    cfg_compound_arch_verdict(&args[0], target_arch)
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

fn strip_inactive_cfg_arch_imports_in_stmts(stmts: &mut Vec<Node>, target_arch: TargetArch) {
    use simple_parser::ast::{
        Attribute, ContractBlock, ContractClause, Decorator, DeferBody, Expr, FStringPart, Field,
        FunctionDef, MacroArg, MacroContractItem, MacroIntroSpec, MacroStmt, Parameter, SkipBody,
        TensorMode, TensorSlice, TensorSliceContent,
    };

    fn strip_in_expr(expr: &mut Expr, target_arch: TargetArch) {
        match expr {
            Expr::FString { parts, .. } => {
                for part in parts {
                    match part {
                        FStringPart::Expr(expr) | FStringPart::ExprWithFormat(expr, _) => {
                            strip_in_expr(expr, target_arch);
                        }
                        FStringPart::Literal(_) => {}
                    }
                }
            }
            Expr::I18nTemplate { parts, args, .. } => {
                for part in parts {
                    match part {
                        FStringPart::Expr(expr) | FStringPart::ExprWithFormat(expr, _) => {
                            strip_in_expr(expr, target_arch);
                        }
                        FStringPart::Literal(_) => {}
                    }
                }
                for (_, expr) in args {
                    strip_in_expr(expr, target_arch);
                }
            }
            Expr::Call { callee, args } => {
                strip_in_expr(callee, target_arch);
                for arg in args {
                    strip_in_expr(&mut arg.value, target_arch);
                }
            }
            Expr::KernelLaunch {
                kernel,
                grid,
                block,
                args,
            } => {
                strip_in_expr(kernel, target_arch);
                strip_in_expr(grid, target_arch);
                strip_in_expr(block, target_arch);
                for arg in args {
                    strip_in_expr(&mut arg.value, target_arch);
                }
            }
            Expr::MethodCall { receiver, args, .. } | Expr::OptionalMethodCall { receiver, args, .. } => {
                strip_in_expr(receiver, target_arch);
                for arg in args {
                    strip_in_expr(&mut arg.value, target_arch);
                }
            }
            Expr::Lambda { body, .. } => strip_in_expr(body, target_arch),
            Expr::DoBlock(nodes) | Expr::UnsafeBlock(nodes, _) => {
                strip_inactive_cfg_arch_imports_in_stmts(nodes, target_arch);
            }
            Expr::Binary { left, right, .. } => {
                strip_in_expr(left, target_arch);
                strip_in_expr(right, target_arch);
            }
            Expr::Unary { operand, .. } => strip_in_expr(operand, target_arch),
            Expr::Index { receiver, index } => {
                strip_in_expr(receiver, target_arch);
                strip_in_expr(index, target_arch);
            }
            Expr::FieldAccess { receiver, .. } | Expr::TupleIndex { receiver, .. } => {
                strip_in_expr(receiver, target_arch);
            }
            Expr::Tuple(items) | Expr::Array(items) | Expr::VecLiteral(items) => {
                for item in items {
                    strip_in_expr(item, target_arch);
                }
            }
            Expr::LabeledTuple(items) => {
                for item in items {
                    strip_in_expr(&mut item.value, target_arch);
                }
            }
            Expr::ArrayRepeat { value, count } => {
                strip_in_expr(value, target_arch);
                strip_in_expr(count, target_arch);
            }
            Expr::GenericInst { expr, .. } => strip_in_expr(expr, target_arch),
            Expr::Dict(items) => {
                for (key, value) in items {
                    strip_in_expr(key, target_arch);
                    strip_in_expr(value, target_arch);
                }
            }
            Expr::ListComprehension {
                expr,
                iterable,
                condition,
                ..
            } => {
                strip_in_expr(expr, target_arch);
                strip_in_expr(iterable, target_arch);
                if let Some(condition) = condition {
                    strip_in_expr(condition, target_arch);
                }
            }
            Expr::DictComprehension {
                key,
                value,
                iterable,
                condition,
                ..
            } => {
                strip_in_expr(key, target_arch);
                strip_in_expr(value, target_arch);
                strip_in_expr(iterable, target_arch);
                if let Some(condition) = condition {
                    strip_in_expr(condition, target_arch);
                }
            }
            Expr::Slice {
                receiver,
                start,
                end,
                step,
            } => {
                strip_in_expr(receiver, target_arch);
                for bound in [start.as_deref_mut(), end.as_deref_mut(), step.as_deref_mut()]
                    .into_iter()
                    .flatten()
                {
                    strip_in_expr(bound, target_arch);
                }
            }
            Expr::StructInit { fields, spread, .. } => {
                for (_, value) in fields {
                    strip_in_expr(value, target_arch);
                }
                if let Some(spread) = spread {
                    strip_in_expr(spread, target_arch);
                }
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                strip_in_expr(condition, target_arch);
                strip_in_expr(then_branch, target_arch);
                if let Some(branch) = else_branch {
                    strip_in_expr(branch, target_arch);
                }
            }
            Expr::Match { subject, arms } => {
                strip_in_expr(subject, target_arch);
                for arm in arms {
                    if let Some(guard) = &mut arm.guard {
                        strip_in_expr(guard, target_arch);
                    }
                    strip_inactive_cfg_arch_imports_in_stmts(&mut arm.body.statements, target_arch);
                }
            }
            Expr::Spread(expr)
            | Expr::DictSpread(expr)
            | Expr::StructSpread(expr)
            | Expr::Spawn(expr)
            | Expr::Await(expr)
            | Expr::Try(expr)
            | Expr::ForceUnwrap(expr)
            | Expr::ExistsCheck(expr)
            | Expr::ContractOld(expr)
            | Expr::New { expr, .. }
            | Expr::Cast { expr, .. }
            | Expr::CastOrReturn { expr, .. }
            | Expr::OptionalChain { expr, .. }
            | Expr::VolatileAccess { address: expr, .. } => strip_in_expr(expr, target_arch),
            Expr::UnwrapOrReturn { expr, default }
            | Expr::UnwrapOr { expr, default }
            | Expr::CastOr { expr, default, .. }
            | Expr::Coalesce { expr, default } => {
                strip_in_expr(expr, target_arch);
                strip_in_expr(default, target_arch);
            }
            Expr::UnwrapElse { expr, fallback_fn } | Expr::CastElse { expr, fallback_fn, .. } => {
                strip_in_expr(expr, target_arch);
                strip_in_expr(fallback_fn, target_arch);
            }
            Expr::Yield(expr) => {
                if let Some(expr) = expr {
                    strip_in_expr(expr, target_arch);
                }
            }
            Expr::Go { args, body, .. } => {
                for arg in args {
                    strip_in_expr(arg, target_arch);
                }
                strip_in_expr(body, target_arch);
            }
            Expr::Range { start, end, .. } => {
                if let Some(start) = start {
                    strip_in_expr(start, target_arch);
                }
                if let Some(end) = end {
                    strip_in_expr(end, target_arch);
                }
            }
            Expr::FunctionalUpdate { target, args, .. } => {
                strip_in_expr(target, target_arch);
                for arg in args {
                    strip_in_expr(&mut arg.value, target_arch);
                }
            }
            Expr::MacroInvocation { args, .. } => {
                for MacroArg::Expr(expr) in args {
                    strip_in_expr(expr, target_arch);
                }
            }
            Expr::Forall { range, predicate, .. } | Expr::Exists { range, predicate, .. } => {
                strip_in_expr(range, target_arch);
                strip_in_expr(predicate, target_arch);
            }
            Expr::GridLiteral { rows, .. } => {
                for row in rows {
                    for expr in row {
                        strip_in_expr(expr, target_arch);
                    }
                }
            }
            Expr::TensorLiteral { mode, .. } => match mode.as_mut() {
                TensorMode::Flat { default, values } => {
                    if let Some(default) = default {
                        strip_in_expr(default, target_arch);
                    }
                    for row in values {
                        for expr in row {
                            strip_in_expr(expr, target_arch);
                        }
                    }
                }
                TensorMode::Slice(slices) => {
                    fn strip_in_slices(slices: &mut [TensorSlice], target_arch: TargetArch) {
                        for slice in slices {
                            match &mut slice.content {
                                TensorSliceContent::NestedSlices(nested) => strip_in_slices(nested, target_arch),
                                TensorSliceContent::GridRows(rows) => {
                                    for row in rows {
                                        for expr in row {
                                            strip_in_expr(expr, target_arch);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    strip_in_slices(slices, target_arch);
                }
            },
            _ => {}
        }
    }

    fn strip_in_attributes(attributes: &mut [Attribute], target_arch: TargetArch) {
        for attribute in attributes {
            if let Some(value) = &mut attribute.value {
                strip_in_expr(value, target_arch);
            }
            if let Some(args) = &mut attribute.args {
                for arg in args {
                    strip_in_expr(arg, target_arch);
                }
            }
            if let Some(args) = &mut attribute.named_args {
                for (_, value) in args {
                    strip_in_expr(value, target_arch);
                }
            }
        }
    }

    fn strip_in_decorators(decorators: &mut [Decorator], target_arch: TargetArch) {
        for decorator in decorators {
            strip_in_expr(&mut decorator.name, target_arch);
            if let Some(args) = &mut decorator.args {
                for arg in args {
                    strip_in_expr(&mut arg.value, target_arch);
                }
            }
        }
    }

    fn strip_in_parameters(parameters: &mut [Parameter], target_arch: TargetArch) {
        for parameter in parameters {
            if let Some(default) = &mut parameter.default {
                strip_in_expr(default, target_arch);
            }
        }
    }

    fn strip_in_fields(fields: &mut [Field], target_arch: TargetArch) {
        for field in fields {
            if let Some(default) = &mut field.default {
                strip_in_expr(default, target_arch);
            }
        }
    }

    fn strip_in_clause(clause: &mut ContractClause, target_arch: TargetArch) {
        strip_in_expr(&mut clause.condition, target_arch);
    }

    fn strip_in_contract(contract: &mut ContractBlock, target_arch: TargetArch) {
        for clause in contract
            .preconditions
            .iter_mut()
            .chain(&mut contract.invariants)
            .chain(&mut contract.postconditions)
            .chain(&mut contract.error_postconditions)
            .chain(contract.decrease_measure.iter_mut())
        {
            strip_in_clause(clause, target_arch);
        }
    }

    fn strip_in_macro_intro(spec: &mut MacroIntroSpec, target_arch: TargetArch) {
        match spec {
            MacroIntroSpec::Decl(_) => {}
            MacroIntroSpec::For { range, body, .. } => {
                strip_in_expr(&mut range.start, target_arch);
                strip_in_expr(&mut range.end, target_arch);
                for spec in body {
                    strip_in_macro_intro(spec, target_arch);
                }
            }
            MacroIntroSpec::If {
                condition,
                then_body,
                else_body,
            } => {
                strip_in_expr(condition, target_arch);
                for spec in then_body.iter_mut().chain(else_body.iter_mut()) {
                    strip_in_macro_intro(spec, target_arch);
                }
            }
        }
    }

    fn strip_in_function(function: &mut FunctionDef, target_arch: TargetArch) {
        strip_in_parameters(&mut function.params, target_arch);
        strip_in_decorators(&mut function.decorators, target_arch);
        strip_in_attributes(&mut function.attributes, target_arch);
        if let Some(contract) = &mut function.contract {
            strip_in_contract(contract, target_arch);
        }
        if let Some(constraint) = &mut function.return_constraint {
            strip_in_expr(constraint, target_arch);
        }
        strip_inactive_cfg_arch_imports_in_stmts(&mut function.body.statements, target_arch);
        if let Some(bounds) = &mut function.bounds_block {
            for case in &mut bounds.cases {
                strip_inactive_cfg_arch_imports_in_stmts(&mut case.body.statements, target_arch);
            }
        }
    }

    fn strip_in_node(stmt: &mut Node, target_arch: TargetArch) {
        match stmt {
            Node::Function(f) => strip_in_function(f, target_arch),
            Node::ModDecl(m) => {
                strip_in_attributes(&mut m.attributes, target_arch);
                if let Some(body) = &mut m.body {
                    strip_inactive_cfg_arch_fn_nodes(body, target_arch);
                }
            }
            Node::Class(def) => {
                strip_in_fields(&mut def.fields, target_arch);
                strip_in_attributes(&mut def.attributes, target_arch);
                if let Some(invariant) = &mut def.invariant {
                    for clause in &mut invariant.conditions {
                        strip_in_clause(clause, target_arch);
                    }
                }
                for invocation in &mut def.macro_invocations {
                    for MacroArg::Expr(expr) in &mut invocation.args {
                        strip_in_expr(expr, target_arch);
                    }
                }
                for method in &mut def.methods {
                    strip_in_function(method, target_arch);
                }
            }
            Node::Struct(def) => {
                strip_in_fields(&mut def.fields, target_arch);
                strip_in_attributes(&mut def.attributes, target_arch);
                if let Some(invariant) = &mut def.invariant {
                    for clause in &mut invariant.conditions {
                        strip_in_clause(clause, target_arch);
                    }
                }
                for method in &mut def.methods {
                    strip_in_function(method, target_arch);
                }
            }
            Node::Bitfield(def) => {
                for constant in &mut def.constants {
                    strip_in_expr(&mut constant.value, target_arch);
                }
                strip_in_attributes(&mut def.attributes, target_arch);
            }
            Node::Enum(def) => {
                for variant in &mut def.variants {
                    if let Some(discriminant) = &mut variant.discriminant {
                        strip_in_expr(discriminant, target_arch);
                    }
                }
                strip_in_attributes(&mut def.attributes, target_arch);
                for method in &mut def.methods {
                    strip_in_function(method, target_arch);
                }
            }
            Node::Trait(def) => {
                for method in &mut def.methods {
                    strip_in_function(method, target_arch);
                }
            }
            Node::Impl(def) => {
                strip_in_attributes(&mut def.attributes, target_arch);
                for method in &mut def.methods {
                    strip_in_function(method, target_arch);
                }
            }
            Node::Mixin(def) => {
                strip_in_fields(&mut def.fields, target_arch);
                for method in &mut def.methods {
                    strip_in_function(method, target_arch);
                }
            }
            Node::Actor(def) => {
                strip_in_fields(&mut def.fields, target_arch);
                for method in &mut def.methods {
                    strip_in_function(method, target_arch);
                }
            }
            Node::TypeAlias(def) => {
                if let Some(predicate) = &mut def.where_clause {
                    strip_in_expr(predicate, target_arch);
                }
            }
            Node::ClassAlias(def) => strip_in_decorators(&mut def.decorators, target_arch),
            Node::FunctionAlias(def) => strip_in_decorators(&mut def.decorators, target_arch),
            Node::Extern(def) => {
                strip_in_parameters(&mut def.params, target_arch);
                strip_in_attributes(&mut def.attributes, target_arch);
            }
            Node::ExternClass(def) => {
                strip_in_attributes(&mut def.attributes, target_arch);
                for method in &mut def.methods {
                    strip_in_parameters(&mut method.params, target_arch);
                    strip_in_attributes(&mut method.attributes, target_arch);
                }
            }
            Node::Macro(def) => {
                for item in &mut def.contract {
                    if let MacroContractItem::Intro(intro) = item {
                        strip_in_macro_intro(&mut intro.spec, target_arch);
                    }
                }
                def.body.retain(|statement| match statement {
                    MacroStmt::Stmt(Node::UseStmt(u)) => !fn_inactive_cfg_arch(&u.attributes, target_arch),
                    MacroStmt::Stmt(Node::MultiUse(m)) => !fn_inactive_cfg_arch(&m.attributes, target_arch),
                    MacroStmt::Stmt(Node::ExportUseStmt(e)) => !fn_inactive_cfg_arch(&e.attributes, target_arch),
                    _ => true,
                });
                for statement in &mut def.body {
                    match statement {
                        MacroStmt::ConstEval(block) | MacroStmt::Emit { block, .. } => {
                            strip_inactive_cfg_arch_imports_in_stmts(&mut block.statements, target_arch);
                        }
                        MacroStmt::Stmt(node) => strip_in_node(node, target_arch),
                    }
                }
            }
            Node::UnitFamily(def) => {
                if let Some(arithmetic) = &mut def.arithmetic {
                    for function in &mut arithmetic.custom_fns {
                        strip_in_function(function, target_arch);
                    }
                }
            }
            Node::CompoundUnit(def) => {
                if let Some(arithmetic) = &mut def.arithmetic {
                    for function in &mut arithmetic.custom_fns {
                        strip_in_function(function, target_arch);
                    }
                }
            }
            Node::Extend(def) => {
                for method in &mut def.methods {
                    strip_in_function(method, target_arch);
                }
            }
            Node::LiteralFunction(def) => {
                strip_inactive_cfg_arch_imports_in_stmts(&mut def.body.statements, target_arch);
            }
            Node::DomainBlock(def) => strip_in_attributes(&mut def.attributes, target_arch),
            Node::MockDecl(def) => {
                for expectation in &mut def.expectations {
                    strip_in_parameters(&mut expectation.params, target_arch);
                    strip_inactive_cfg_arch_imports_in_stmts(&mut expectation.body, target_arch);
                }
            }
            Node::Expression(expr) => strip_in_expr(expr, target_arch),
            Node::Let(stmt) => {
                if let Some(expr) = &mut stmt.value {
                    strip_in_expr(expr, target_arch);
                }
            }
            Node::Const(stmt) => strip_in_expr(&mut stmt.value, target_arch),
            Node::Static(stmt) => strip_in_expr(&mut stmt.value, target_arch),
            Node::Assignment(stmt) => {
                strip_in_expr(&mut stmt.target, target_arch);
                strip_in_expr(&mut stmt.value, target_arch);
            }
            Node::Return(stmt) => {
                if let Some(expr) = &mut stmt.value {
                    strip_in_expr(expr, target_arch);
                }
            }
            Node::Break(stmt) => {
                if let Some(expr) = &mut stmt.value {
                    strip_in_expr(expr, target_arch);
                }
            }
            Node::Guard(stmt) => {
                if let Some(condition) = &mut stmt.condition {
                    strip_in_expr(condition, target_arch);
                }
                strip_in_expr(&mut stmt.result, target_arch);
            }
            Node::Assert(stmt) => strip_in_expr(&mut stmt.condition, target_arch),
            Node::Assume(stmt) => strip_in_expr(&mut stmt.condition, target_arch),
            Node::Admit(stmt) => strip_in_expr(&mut stmt.condition, target_arch),
            Node::Calc(stmt) => {
                for step in &mut stmt.steps {
                    strip_in_expr(&mut step.expr, target_arch);
                }
            }
            Node::If(if_stmt) => {
                strip_in_expr(&mut if_stmt.condition, target_arch);
                strip_inactive_cfg_arch_imports_in_stmts(&mut if_stmt.then_block.statements, target_arch);
                for (_, condition, block) in &mut if_stmt.elif_branches {
                    strip_in_expr(condition, target_arch);
                    strip_inactive_cfg_arch_imports_in_stmts(&mut block.statements, target_arch);
                }
                if let Some(else_block) = &mut if_stmt.else_block {
                    strip_inactive_cfg_arch_imports_in_stmts(&mut else_block.statements, target_arch);
                }
            }
            Node::Match(m) => {
                strip_in_expr(&mut m.subject, target_arch);
                for arm in &mut m.arms {
                    if let Some(guard) = &mut arm.guard {
                        strip_in_expr(guard, target_arch);
                    }
                    strip_inactive_cfg_arch_imports_in_stmts(&mut arm.body.statements, target_arch);
                }
            }
            Node::For(f) => {
                strip_in_expr(&mut f.iterable, target_arch);
                for clause in &mut f.invariants {
                    strip_in_clause(clause, target_arch);
                }
                strip_inactive_cfg_arch_imports_in_stmts(&mut f.body.statements, target_arch);
            }
            Node::While(w) => {
                strip_in_expr(&mut w.condition, target_arch);
                for clause in &mut w.invariants {
                    strip_in_clause(clause, target_arch);
                }
                strip_inactive_cfg_arch_imports_in_stmts(&mut w.body.statements, target_arch);
            }
            Node::Loop(l) => strip_inactive_cfg_arch_imports_in_stmts(&mut l.body.statements, target_arch),
            Node::Context(stmt) => {
                strip_in_expr(&mut stmt.context, target_arch);
                strip_inactive_cfg_arch_imports_in_stmts(&mut stmt.body.statements, target_arch);
            }
            Node::With(stmt) => {
                strip_in_expr(&mut stmt.resource, target_arch);
                strip_inactive_cfg_arch_imports_in_stmts(&mut stmt.body.statements, target_arch);
            }
            Node::Skip(stmt) => {
                if let SkipBody::Block(block) = &mut stmt.body {
                    strip_inactive_cfg_arch_imports_in_stmts(&mut block.statements, target_arch);
                }
            }
            Node::Defer(stmt) => match &mut stmt.body {
                DeferBody::Expr(expr) => strip_in_expr(expr, target_arch),
                DeferBody::Block(block) => {
                    strip_inactive_cfg_arch_imports_in_stmts(&mut block.statements, target_arch);
                }
            },
            Node::ErrDefer(stmt) => match &mut stmt.body {
                DeferBody::Expr(expr) => strip_in_expr(expr, target_arch),
                DeferBody::Block(block) => {
                    strip_inactive_cfg_arch_imports_in_stmts(&mut block.statements, target_arch);
                }
            },
            Node::InlineAsm(stmt) => {
                for constraint in &mut stmt.constraints {
                    if let Some(operand) = &mut constraint.operand {
                        strip_in_expr(operand, target_arch);
                    }
                }
            }
            _ => {}
        }
    }

    stmts.retain(|stmt| match stmt {
        Node::UseStmt(u) => !fn_inactive_cfg_arch(&u.attributes, target_arch),
        Node::MultiUse(m) => !fn_inactive_cfg_arch(&m.attributes, target_arch),
        Node::ExportUseStmt(e) => !fn_inactive_cfg_arch(&e.attributes, target_arch),
        _ => true,
    });
    for stmt in stmts.iter_mut() {
        strip_in_node(stmt, target_arch);
    }
}

/// Drop top-level `@cfg(<arch>)`-gated function and import nodes whose
/// architecture does not match `target_arch`, recording stripped function names
/// and warning about duplicate active variants. Item-list form shared by
/// module- and interpreter-level callers.
pub fn strip_inactive_cfg_arch_fn_nodes(items: &mut Vec<Node>, target_arch: TargetArch) {
    items.retain(|item| match item {
        Node::Function(f) => {
            if fn_inactive_cfg_arch(&f.attributes, target_arch) {
                note_stripped_fn(&f.name);
                return false;
            }
            true
        }
        Node::UseStmt(u) => !fn_inactive_cfg_arch(&u.attributes, target_arch),
        Node::MultiUse(m) => !fn_inactive_cfg_arch(&m.attributes, target_arch),
        Node::ExportUseStmt(e) => !fn_inactive_cfg_arch(&e.attributes, target_arch),
        _ => true,
    });
    strip_inactive_cfg_arch_imports_in_stmts(items, target_arch);
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
    use simple_common::target::TargetOS;

    fn linux_host() -> CfgTarget {
        CfgTarget::new("linux", TargetArch::host().name())
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
        // Unbalanced blocks are left untouched; the parser's own lexer-side
        // mask then fails closed on them (`cond_compile` `balanced == false`
        // is a syntax error), so neither branch is ever compiled.
        let malformed = "@when(os=\"windows\"):\nval A = 1\n";
        assert_eq!(strip_inactive_cfg_arch_globals(malformed, TargetArch::host()), malformed);
        assert!(simple_parser::Parser::new(malformed).parse().is_err());
    }

    #[test]
    fn os_when_path_identity_selects_nested_platform_owner() {
        let source = include_str!("../../../../lib/nogc_sync_mut/io/path_identity_abi.spl");
        // The POSIX errno owner lives in `_PathIdentityPosix/errno_abi.spl` and is
        // imported only by the non-Windows branch.
        let posix_errno = "use std.nogc_sync_mut.io._PathIdentityPosix.errno_abi.{path_errno_address}";
        for (os, expected, excluded) in [
            ("linux", posix_errno, "fn path_errno_address() -> i64: 0"),
            ("freebsd", posix_errno, "fn path_errno_address() -> i64: 0"),
            ("macos", posix_errno, "fn path_errno_address() -> i64: 0"),
            ("windows", "fn path_errno_address() -> i64: 0", posix_errno),
        ] {
            let filtered = super::strip_os_when_blocks(source, &CfgTarget::new(os, TargetArch::host().name())).expect("platform owner branch");
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
            ("windows", "    11", "    22"),
            ("linux", "    22", "    11"),
        ] {
            let filtered = super::strip_os_when_blocks(source, &CfgTarget::new(os, TargetArch::host().name())).expect("supported OS block");
            assert_eq!(filtered.lines().count(), source.lines().count());
            assert!(filtered.contains(expected));
            assert!(!filtered.contains(excluded));
            assert!(simple_parser::Parser::new(&filtered).parse().is_ok());
        }
        // Unknown atoms evaluate false, like the lexer: the block is dropped.
        let unknown = super::strip_os_when_blocks("@when(os=\"unknown\"):\nfn u() -> i64: 1\n@end\n", &linux_host())
            .expect("unknown atom is false, not an error");
        assert!(!unknown.contains("fn u"));
        // @elif selects the first matching branch (previously rejected).
        let elif = "@when(os=\"windows\"):\nfn e() -> i64: 1\n@elif(os=\"linux\"):\nfn e() -> i64: 2\n@else:\nfn e() -> i64: 3\n@end\n";
        let linux = super::strip_os_when_blocks(elif, &linux_host()).expect("elif block");
        assert!(linux.contains("fn e() -> i64: 2") && !linux.contains(": 1") && !linux.contains(": 3"));
        assert_eq!(linux.lines().count(), elif.lines().count());
        // Unbalanced structure still fails closed.
        assert!(super::strip_os_when_blocks("@else:\n", &linux_host()).is_err());
        assert!(super::strip_os_when_blocks("@end\n", &linux_host()).is_err());
        assert!(super::strip_os_when_blocks("@when(os=\"windows\"):\n", &linux_host()).is_err());
        assert!(super::strip_os_when_blocks("@elif(os=\"windows\"):\n", &linux_host()).is_err());
        // A duplicate @else, an @elif after @else and an empty condition are
        // structural errors too: never silently drop or double a branch.
        let dup_else = "@when(os=\"windows\"):\nval A = 1\n@else:\nval A = 2\n@else:\nval A = 3\n@end\n";
        assert!(super::strip_os_when_blocks(dup_else, &linux_host()).unwrap_err().contains("duplicate @else"));
        let elif_after_else = "@when(os=\"windows\"):\nval A = 1\n@else:\nval A = 2\n@elif(os=\"linux\"):\nval A = 3\n@end\n";
        assert!(super::strip_os_when_blocks(elif_after_else, &linux_host()).unwrap_err().contains("@elif after @else"));
        assert!(super::strip_os_when_blocks("@when():\nval A = 1\n@end\n", &linux_host()).unwrap_err().contains("empty @when"));
        assert!(simple_parser::Parser::new(dup_else).parse().is_err());
        let nested = "@when(os=\"windows\"):\n@when(os=\"windows\"):\nval SELECTED = 11\n@else:\nval SELECTED = 22\n@end\n@else:\nval SELECTED = 33\n@end\n";
        let windows = super::strip_os_when_blocks(nested, &CfgTarget::new("windows", TargetArch::host().name())).expect("nested Windows branch");
        let linux = super::strip_os_when_blocks(nested, &linux_host()).expect("nested Linux fallback");
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

    #[test]
    fn inactive_cfg_arch_top_level_use_is_blanked_before_dependency_collection() {
        // seed_cfg_on_top_level_use_ignored_2026-11-21: `@cfg(riscv64)\nuse ...`
        // leaked riscv modules into aarch64 kernel closures.
        let source = "@cfg(riscv64)\nuse os.kernel.arch.riscv64.console.{serial_read_byte}\n@cfg(arm64)\nuse os.kernel.arch.arm.pl011_common.{pl011_write_byte}\n@cfg(not(riscv64))\npub use os.a.{\n    b,\n    c\n}\n@cfg(x86_64)\nexport y from os.x\n@cfg(riscv32)\nimport os.rv32.thing\n@cfg(x86)\nuse = 3\nfn keep() -> i64:\n    1\n";
        let arm = strip_inactive_cfg_arch_globals(source, TargetArch::Aarch64);
        assert_eq!(arm.lines().count(), source.lines().count());
        assert!(!arm.contains("riscv64.console"), "{arm}");
        assert!(arm.contains("pl011_common") && arm.contains("pub use os.a.{") && arm.contains("    c"));
        assert!(!arm.contains("from os.x") && !arm.contains("os.rv32.thing"));
        // `use = 3` is an expression, not an import: left for the parser.
        assert!(arm.contains("use = 3"));
        assert!(arm.contains("fn keep"));
        let rv = strip_inactive_cfg_arch_globals(source, TargetArch::Riscv64);
        assert!(rv.contains("riscv64.console") && !rv.contains("pl011_common"));
        assert!(!rv.contains("os.a.{") && !rv.contains("    b,") && !rv.contains("@cfg(riscv64)"));
        // Indented (function-local) uses are not touched by this pass.
        let local = "fn f():\n    @cfg(riscv64)\n    use a.b\n";
        assert_eq!(strip_inactive_cfg_arch_globals(local, TargetArch::Aarch64), local);
    }

    #[test]
    fn compound_arch_cfg_evaluates_not_or_and_all_any_and_leaves_non_arch_ungated() {
        let source = "\
@cfg(x86_64)
fn pick() -> i64:
    1
@cfg(x86)
fn pick() -> i64:
    2
@cfg(not(x86_64 or x86))
fn pick() -> i64:
    3
@cfg(any(aarch64, riscv64))
fn wide_arm_or_rv() -> i64:
    4
@cfg(all(not(x86_64), not(x86)))
fn non_x86_all() -> i64:
    5
@cfg(x86_64 or baremetal)
fn mixed_stays_ungated() -> i64:
    6
";
        let surviving_fns = |arch: TargetArch| -> Vec<(String, i64)> {
            let mut module = parse_cfg_filtered_module(source, arch).expect("parse compound cfg");
            module
                .items
                .drain(..)
                .filter_map(|item| match item {
                    Node::Function(f) => {
                        let Some(Node::Expression(simple_parser::ast::Expr::Integer(v))) = f.body.statements.first()
                        else {
                            panic!("expected integer body");
                        };
                        Some((f.name, *v))
                    }
                    _ => None,
                })
                .collect()
        };

        assert_eq!(
            surviving_fns(TargetArch::X86_64),
            vec![("pick".into(), 1), ("mixed_stays_ungated".into(), 6)]
        );
        assert_eq!(
            surviving_fns(TargetArch::X86),
            vec![("pick".into(), 2), ("mixed_stays_ungated".into(), 6)]
        );
        assert_eq!(
            surviving_fns(TargetArch::Riscv64),
            vec![
                ("pick".into(), 3),
                ("wide_arm_or_rv".into(), 4),
                ("non_x86_all".into(), 5),
                ("mixed_stays_ungated".into(), 6),
            ]
        );
        assert_eq!(
            surviving_fns(TargetArch::Arm),
            vec![
                ("pick".into(), 3),
                ("non_x86_all".into(), 5),
                ("mixed_stays_ungated".into(), 6),
            ]
        );
    }

    #[test]
    fn cfg_gated_top_level_use_and_export_use_strip_inactive_arches() {
        let source = "\
@cfg(x86_64)
use os.kernel.arch.x86.com1_common.{x86_com1_read_byte}
@cfg(riscv64)
use os.kernel.arch.riscv64.console.{serial_read_byte}
@cfg(arm64)
export use os.kernel.arch.arm.pl011_common.{pl011_write_byte}
@cfg(not(x86_64 or x86))
use os.kernel.hal.generic_timer
";
        let kept_paths = |arch: TargetArch| -> Vec<String> {
            let module = parse_cfg_filtered_module(source, arch).expect("parse cfg use");
            module
                .items
                .iter()
                .filter_map(|item| match item {
                    Node::UseStmt(u) => {
                        let mut segs = u.path.segments.clone();
                        if let simple_parser::ast::ImportTarget::Single(last) = &u.target {
                            segs.push(last.clone());
                        }
                        Some(segs.join("."))
                    }
                    Node::ExportUseStmt(e) => Some(format!("export:{}", e.path.segments.join("."))),
                    _ => None,
                })
                .collect()
        };

        assert_eq!(kept_paths(TargetArch::X86_64), vec!["os.kernel.arch.x86.com1_common"]);
        assert_eq!(
            kept_paths(TargetArch::Riscv64),
            vec!["os.kernel.arch.riscv64.console", "os.kernel.hal.generic_timer"]
        );
        assert_eq!(
            kept_paths(TargetArch::Aarch64),
            vec![
                "export:os.kernel.arch.arm.pl011_common",
                "os.kernel.hal.generic_timer"
            ]
        );
    }
}
