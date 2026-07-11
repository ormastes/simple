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
//! preprocessor (`parser_preprocessor.spl` `_pp_cfg_condition_matches`). Only
//! functions are filtered -- a wrong-arch `@cfg` `use`/`extern`/`const` is
//! harmless (an unused declaration) and dropping those risks perturbing import
//! resolution.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use simple_common::target::TargetArch;
use simple_parser::ast::{Attribute, Node};

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
        Expr::Call { callee, args: call_args } => {
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
