//! File discovery: full-scan and entry-closure based .spl file discovery,
//! reachable module path extraction, file deduplication.

use std::collections::{BTreeMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};

#[cfg(test)]
use simple_common::target::TargetArch;

use super::{
    collect_spl_files_recursive, native_project_rust_trace_enabled, safe_canonicalize, same_file_path,
    NativeProjectBuilder,
};

// `@cfg(<arch>)` evaluation + function-variant stripping now live in the
// shared `pipeline::cfg_strip` module so the `bin/simple run` JIT/interpreter
// paths apply the same filter as native-project builds (bug
// `x64_freestanding_cfg_multivariant_misdispatch`). Re-exported here for the
// existing native_project call sites (compiler.rs, imports.rs, tests.rs).
pub(crate) use crate::pipeline::cfg_strip::strip_inactive_cfg_arch_fns;
#[cfg(test)]
use crate::pipeline::cfg_strip::cfg_name_to_arch;

/// Test-only recognition of a leading arch cfg.
///
/// This is deliberately not a production file gate: Simple `@cfg` applies to
/// the following declaration, so an inactive first declaration must not hide
/// later active declarations in the same file.
/// Extract the arch-gating verdict for a `.spl` source, if its first
/// meaningful line is a whole-file `@cfg(<arch>)` (optionally
/// `@cfg(not(<arch>))`) decorator.
///
/// Returns `Some(true)` if the file should be included for `target_arch`,
/// `Some(false)` if it should be excluded, and `None` if the file has no
/// leading arch cfg gate (not `@cfg`-decorated at all, or gated on a
/// non-arch condition) -- callers should treat `None` as "always include",
/// matching today's behavior for every file that isn't gated this way.
///
/// This intentionally only recognizes a single leading `@cfg(...)` line, not
/// the full per-declaration preprocessor grammar (multi-line brace tracking,
/// nested conditions, etc.) -- that full evaluation already exists in
/// `parser_preprocessor.spl` and is out of scope to reimplement here. The
/// narrower goal is just to stop native-project discovery from being
/// completely blind to the common "this whole file is one arch's HAL
/// implementation" pattern documented in `src/os/kernel/arch/hal.spl`.
#[cfg(test)]
pub(crate) fn file_arch_cfg_gate(source: &str, target_arch: TargetArch) -> Option<bool> {
    for line in source.lines() {
        let trimmed = line.trim_start();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        if !trimmed.starts_with("@cfg(") {
            return None;
        }
        let inner = trimmed.strip_prefix("@cfg(")?.trim_end();
        let inner = inner.strip_suffix(')').unwrap_or(inner);
        // Skip `"key", "value"` style conditions (e.g. @cfg("target_arch", "arm")) --
        // not a bare arch alias, leave ungated.
        if inner.contains(',') || inner.contains('"') {
            return None;
        }
        let (negate, name) = match inner.strip_prefix("not(") {
            Some(rest) => (true, rest.trim_end_matches(')').trim()),
            None => (false, inner.trim()),
        };
        return cfg_name_to_arch(name).map(|arch| {
            let matches = arch == target_arch;
            if negate {
                !matches
            } else {
                matches
            }
        });
    }
    None
}

fn import_target_names(target: &simple_parser::ast::ImportTarget, names: &mut Vec<String>) {
    use simple_parser::ast::ImportTarget;
    match target {
        ImportTarget::Single(name) => names.push(name.clone()),
        ImportTarget::Aliased { alias, .. } => names.push(alias.clone()),
        ImportTarget::Group(items) => {
            for item in items {
                import_target_names(item, names);
            }
        }
        ImportTarget::Glob => {}
    }
}

fn import_target_has_glob(target: &simple_parser::ast::ImportTarget) -> bool {
    match target {
        simple_parser::ast::ImportTarget::Group(items) => items.iter().any(import_target_has_glob),
        simple_parser::ast::ImportTarget::Glob => true,
        _ => false,
    }
}

fn bare_export_names(items: &[simple_parser::ast::Node]) -> Vec<String> {
    let mut names = Vec::new();
    for item in items {
        if let simple_parser::ast::Node::ExportUseStmt(export) = item {
            if export.path.segments.is_empty() {
                import_target_names(&export.target, &mut names);
            }
        }
    }
    names.sort();
    names.dedup();
    names
}

fn provided_export_names(
    items: &[simple_parser::ast::Node],
    requested: &[String],
) -> (Vec<String>, Vec<String>, Vec<String>, Vec<String>, bool) {
    use simple_parser::ast::{Node, Pattern};

    let mut defined = Vec::new();
    let mut extern_decls = Vec::new();
    let mut imported = Vec::new();
    let mut forwarded = Vec::new();
    let mut imports_all = false;
    let mut forwards_glob = false;
    let bare_exports = bare_export_names(items);
    for item in items {
        match item {
            Node::Function(def) if !def.body.statements.is_empty() => defined.push(def.name.clone()),
            // Extern items are declarations, not definitions: a sibling that
            // re-declares `extern fn foo` to call another module's `fn foo`
            // must not tie as an export provider with the real definition.
            Node::Extern(def) => extern_decls.push(def.name.clone()),
            Node::Class(def) => defined.push(def.name.clone()),
            Node::Struct(def) => defined.push(def.name.clone()),
            Node::Enum(def) => defined.push(def.name.clone()),
            Node::Trait(def) => defined.push(def.name.clone()),
            Node::Let(stmt) => match &stmt.pattern {
                Pattern::Identifier(name) | Pattern::MutIdentifier(name) => defined.push(name.clone()),
                _ => {}
            },
            Node::Const(stmt) => defined.push(stmt.name.clone()),
            Node::Static(stmt) => defined.push(stmt.name.clone()),
            Node::UseStmt(stmt) => {
                imports_all |= import_target_has_glob(&stmt.target);
                import_target_names(&stmt.target, &mut imported);
            }
            Node::MultiUse(stmt) => {
                for (_, target) in &stmt.imports {
                    imports_all |= import_target_has_glob(target);
                    import_target_names(target, &mut imported);
                }
            }
            Node::ExportUseStmt(stmt) if !stmt.path.segments.is_empty() => {
                imports_all |= import_target_has_glob(&stmt.target);
                forwards_glob |= import_target_has_glob(&stmt.target);
                import_target_names(&stmt.target, &mut imported);
                import_target_names(&stmt.target, &mut forwarded);
            }
            _ => {}
        }
    }

    let mut explicit: Vec<String> = requested
        .iter()
        .filter(|name| forwarded.contains(name) || (bare_exports.contains(name) && defined.contains(name)))
        .cloned()
        .collect();
    explicit.sort();
    explicit.dedup();
    let mut definitions: Vec<String> = requested
        .iter()
        .filter(|name| defined.contains(name))
        .cloned()
        .collect();
    definitions.sort();
    definitions.dedup();
    let mut facades: Vec<String> = requested
        .iter()
        .filter(|name| bare_exports.contains(name) && (imports_all || imported.contains(name)))
        .cloned()
        .collect();
    facades.sort();
    facades.dedup();
    let mut extern_weak: Vec<String> = requested
        .iter()
        .filter(|name| extern_decls.contains(name) && !defined.contains(name))
        .cloned()
        .collect();
    extern_weak.sort();
    extern_weak.dedup();
    (explicit, definitions, facades, extern_weak, forwards_glob)
}

pub(crate) fn visit_ast_nodes(nodes: &[simple_parser::ast::Node], visitor: &mut dyn FnMut(&simple_parser::ast::Node)) {
    use simple_parser::ast::{
        Attribute, ContractBlock, ContractClause, Decorator, DeferBody, Expr, Field, FStringPart, MacroArg,
        MacroContractItem, MacroIntroSpec, MacroStmt, Node, Parameter, SkipBody, TensorMode, TensorSliceContent,
    };

    fn visit_expr(expr: &Expr, visitor: &mut dyn FnMut(&Node)) {
        match expr {
            Expr::FString { parts, .. } | Expr::I18nTemplate { parts, .. } => {
                for part in parts {
                    match part {
                        FStringPart::Expr(expr) | FStringPart::ExprWithFormat(expr, _) => visit_expr(expr, visitor),
                        FStringPart::Literal(_) => {}
                    }
                }
                if let Expr::I18nTemplate { args, .. } = expr {
                    for (_, expr) in args {
                        visit_expr(expr, visitor);
                    }
                }
            }
            Expr::Call { callee, args } => {
                visit_expr(callee, visitor);
                for arg in args {
                    visit_expr(&arg.value, visitor);
                }
            }
            Expr::KernelLaunch {
                kernel,
                grid,
                block,
                args,
            } => {
                visit_expr(kernel, visitor);
                visit_expr(grid, visitor);
                visit_expr(block, visitor);
                for arg in args {
                    visit_expr(&arg.value, visitor);
                }
            }
            Expr::MethodCall { receiver, args, .. } => {
                visit_expr(receiver, visitor);
                for arg in args {
                    visit_expr(&arg.value, visitor);
                }
            }
            Expr::Lambda { body, .. } => visit_expr(body, visitor),
            Expr::DoBlock(nodes) | Expr::UnsafeBlock(nodes) => visit_ast_nodes(nodes, visitor),
            Expr::Binary { left, right, .. } => {
                visit_expr(left, visitor);
                visit_expr(right, visitor);
            }
            Expr::Unary { operand, .. } => visit_expr(operand, visitor),
            Expr::Index { receiver, index } => {
                visit_expr(receiver, visitor);
                visit_expr(index, visitor);
            }
            Expr::FieldAccess { receiver, .. } | Expr::TupleIndex { receiver, .. } => visit_expr(receiver, visitor),
            Expr::Tuple(items) | Expr::Array(items) | Expr::VecLiteral(items) => {
                for item in items {
                    visit_expr(item, visitor);
                }
            }
            Expr::LabeledTuple(items) => {
                for item in items {
                    visit_expr(&item.value, visitor);
                }
            }
            Expr::ArrayRepeat { value, count } => {
                visit_expr(value, visitor);
                visit_expr(count, visitor);
            }
            Expr::Dict(items) => {
                for (key, value) in items {
                    visit_expr(key, visitor);
                    visit_expr(value, visitor);
                }
            }
            Expr::ListComprehension {
                expr,
                iterable,
                condition,
                ..
            } => {
                visit_expr(expr, visitor);
                visit_expr(iterable, visitor);
                if let Some(condition) = condition {
                    visit_expr(condition, visitor);
                }
            }
            Expr::DictComprehension {
                key,
                value,
                iterable,
                condition,
                ..
            } => {
                visit_expr(key, visitor);
                visit_expr(value, visitor);
                visit_expr(iterable, visitor);
                if let Some(condition) = condition {
                    visit_expr(condition, visitor);
                }
            }
            Expr::Slice {
                receiver,
                start,
                end,
                step,
            } => {
                visit_expr(receiver, visitor);
                for bound in [start, end, step].into_iter().flatten() {
                    visit_expr(bound, visitor);
                }
            }
            Expr::StructInit { fields, spread, .. } => {
                for (_, value) in fields {
                    visit_expr(value, visitor);
                }
                if let Some(spread) = spread {
                    visit_expr(spread, visitor);
                }
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                visit_expr(condition, visitor);
                visit_expr(then_branch, visitor);
                if let Some(branch) = else_branch {
                    visit_expr(branch, visitor);
                }
            }
            Expr::Match { subject, arms } => {
                visit_expr(subject, visitor);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        visit_expr(guard, visitor);
                    }
                    visit_ast_nodes(&arm.body.statements, visitor);
                }
            }
            Expr::Spread(expr) | Expr::DictSpread(expr) => visit_expr(expr, visitor),
            Expr::Spawn(expr)
            | Expr::Await(expr)
            | Expr::Try(expr)
            | Expr::ForceUnwrap(expr)
            | Expr::ExistsCheck(expr)
            | Expr::UnwrapOrReturn(expr)
            | Expr::ContractOld(expr) => visit_expr(expr, visitor),
            Expr::Yield(expr) => {
                if let Some(expr) = expr {
                    visit_expr(expr, visitor);
                }
            }
            Expr::Go { args, body, .. } => {
                for arg in args {
                    visit_expr(arg, visitor);
                }
                visit_expr(body, visitor);
            }
            Expr::New { expr, .. }
            | Expr::Cast { expr, .. }
            | Expr::CastOrReturn { expr, .. }
            | Expr::OptionalChain { expr, .. }
            | Expr::VolatileAccess { address: expr, .. } => visit_expr(expr, visitor),
            Expr::Range { start, end, .. } => {
                if let Some(start) = start {
                    visit_expr(start, visitor);
                }
                if let Some(end) = end {
                    visit_expr(end, visitor);
                }
            }
            Expr::FunctionalUpdate { target, args, .. } => {
                visit_expr(target, visitor);
                for arg in args {
                    visit_expr(&arg.value, visitor);
                }
            }
            Expr::MacroInvocation { args, .. } => {
                for MacroArg::Expr(expr) in args {
                    visit_expr(expr, visitor);
                }
            }
            Expr::UnwrapOr { expr, default }
            | Expr::CastOr { expr, default, .. }
            | Expr::Coalesce { expr, default } => {
                visit_expr(expr, visitor);
                visit_expr(default, visitor);
            }
            Expr::UnwrapElse { expr, fallback_fn } | Expr::CastElse { expr, fallback_fn, .. } => {
                visit_expr(expr, visitor);
                visit_expr(fallback_fn, visitor);
            }
            Expr::OptionalMethodCall { receiver, args, .. } => {
                visit_expr(receiver, visitor);
                for arg in args {
                    visit_expr(&arg.value, visitor);
                }
            }
            Expr::Forall { range, predicate, .. } | Expr::Exists { range, predicate, .. } => {
                visit_expr(range, visitor);
                visit_expr(predicate, visitor);
            }
            Expr::GridLiteral { rows, .. } => {
                for row in rows {
                    for expr in row {
                        visit_expr(expr, visitor);
                    }
                }
            }
            Expr::TensorLiteral { mode, .. } => match mode.as_ref() {
                TensorMode::Flat { default, values } => {
                    if let Some(default) = default {
                        visit_expr(default, visitor);
                    }
                    for row in values {
                        for expr in row {
                            visit_expr(expr, visitor);
                        }
                    }
                }
                TensorMode::Slice(slices) => {
                    fn visit_slices(slices: &[simple_parser::ast::TensorSlice], visitor: &mut dyn FnMut(&Node)) {
                        for slice in slices {
                            match &slice.content {
                                TensorSliceContent::NestedSlices(slices) => visit_slices(slices, visitor),
                                TensorSliceContent::GridRows(rows) => {
                                    for row in rows {
                                        for expr in row {
                                            visit_expr(expr, visitor);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    visit_slices(slices, visitor);
                }
            },
            _ => {}
        }
    }

    fn visit_attribute(attribute: &Attribute, visitor: &mut dyn FnMut(&Node)) {
        if let Some(value) = &attribute.value {
            visit_expr(value, visitor);
        }
        if let Some(args) = &attribute.args {
            for arg in args {
                visit_expr(arg, visitor);
            }
        }
        if let Some(args) = &attribute.named_args {
            for (_, value) in args {
                visit_expr(value, visitor);
            }
        }
    }

    fn visit_attributes(attributes: &[Attribute], visitor: &mut dyn FnMut(&Node)) {
        for attribute in attributes {
            visit_attribute(attribute, visitor);
        }
    }

    fn visit_decorators(decorators: &[Decorator], visitor: &mut dyn FnMut(&Node)) {
        for decorator in decorators {
            visit_expr(&decorator.name, visitor);
            if let Some(args) = &decorator.args {
                for arg in args {
                    visit_expr(&arg.value, visitor);
                }
            }
        }
    }

    fn visit_parameters(parameters: &[Parameter], visitor: &mut dyn FnMut(&Node)) {
        for parameter in parameters {
            if let Some(default) = &parameter.default {
                visit_expr(default, visitor);
            }
        }
    }

    fn visit_fields(fields: &[Field], visitor: &mut dyn FnMut(&Node)) {
        for field in fields {
            if let Some(default) = &field.default {
                visit_expr(default, visitor);
            }
        }
    }

    fn visit_clause(clause: &ContractClause, visitor: &mut dyn FnMut(&Node)) {
        visit_expr(&clause.condition, visitor);
    }

    fn visit_contract(contract: &ContractBlock, visitor: &mut dyn FnMut(&Node)) {
        for clause in contract
            .preconditions
            .iter()
            .chain(&contract.invariants)
            .chain(&contract.postconditions)
            .chain(&contract.error_postconditions)
            .chain(contract.decreases.iter())
        {
            visit_clause(clause, visitor);
        }
    }

    fn visit_macro_args(args: &[MacroArg], visitor: &mut dyn FnMut(&Node)) {
        for MacroArg::Expr(expr) in args {
            visit_expr(expr, visitor);
        }
    }

    fn visit_macro_intro(spec: &MacroIntroSpec, visitor: &mut dyn FnMut(&Node)) {
        match spec {
            MacroIntroSpec::Decl(_) => {}
            MacroIntroSpec::For { range, body, .. } => {
                visit_expr(&range.start, visitor);
                visit_expr(&range.end, visitor);
                for spec in body {
                    visit_macro_intro(spec, visitor);
                }
            }
            MacroIntroSpec::If {
                condition,
                then_body,
                else_body,
            } => {
                visit_expr(condition, visitor);
                for spec in then_body.iter().chain(else_body) {
                    visit_macro_intro(spec, visitor);
                }
            }
        }
    }

    fn visit_function(function: &simple_parser::ast::FunctionDef, visitor: &mut dyn FnMut(&Node)) {
        visit_parameters(&function.params, visitor);
        visit_decorators(&function.decorators, visitor);
        visit_attributes(&function.attributes, visitor);
        if let Some(contract) = &function.contract {
            visit_contract(contract, visitor);
        }
        if let Some(constraint) = &function.return_constraint {
            visit_expr(constraint, visitor);
        }
        visit_ast_nodes(&function.body.statements, visitor);
        if let Some(bounds) = &function.bounds_block {
            for case in &bounds.cases {
                visit_ast_nodes(&case.body.statements, visitor);
            }
        }
    }

    for node in nodes {
        visitor(node);
        match node {
            Node::Function(function) => visit_function(function, visitor),
            Node::Struct(def) => {
                visit_fields(&def.fields, visitor);
                visit_attributes(&def.attributes, visitor);
                if let Some(invariant) = &def.invariant {
                    invariant
                        .conditions
                        .iter()
                        .for_each(|clause| visit_clause(clause, visitor));
                }
                def.methods.iter().for_each(|method| visit_function(method, visitor));
            }
            Node::Bitfield(def) => {
                for constant in &def.constants {
                    visit_expr(&constant.value, visitor);
                }
                visit_attributes(&def.attributes, visitor);
            }
            Node::Class(def) => {
                visit_fields(&def.fields, visitor);
                visit_attributes(&def.attributes, visitor);
                if let Some(invariant) = &def.invariant {
                    invariant
                        .conditions
                        .iter()
                        .for_each(|clause| visit_clause(clause, visitor));
                }
                for invocation in &def.macro_invocations {
                    visit_macro_args(&invocation.args, visitor);
                }
                def.methods.iter().for_each(|method| visit_function(method, visitor));
            }
            Node::Enum(def) => {
                for variant in &def.variants {
                    if let Some(discriminant) = &variant.discriminant {
                        visit_expr(discriminant, visitor);
                    }
                }
                visit_attributes(&def.attributes, visitor);
                def.methods.iter().for_each(|method| visit_function(method, visitor));
            }
            Node::Trait(def) => def.methods.iter().for_each(|method| visit_function(method, visitor)),
            Node::Impl(def) => {
                visit_attributes(&def.attributes, visitor);
                def.methods.iter().for_each(|method| visit_function(method, visitor));
            }
            Node::Mixin(def) => {
                visit_fields(&def.fields, visitor);
                def.methods.iter().for_each(|method| visit_function(method, visitor));
            }
            Node::Actor(def) => {
                visit_fields(&def.fields, visitor);
                def.methods.iter().for_each(|method| visit_function(method, visitor));
            }
            Node::TypeAlias(def) => {
                if let Some(predicate) = &def.where_clause {
                    visit_expr(predicate, visitor);
                }
            }
            Node::ClassAlias(def) => visit_decorators(&def.decorators, visitor),
            Node::FunctionAlias(def) => visit_decorators(&def.decorators, visitor),
            Node::Extern(def) => {
                visit_parameters(&def.params, visitor);
                visit_attributes(&def.attributes, visitor);
            }
            Node::ExternClass(def) => {
                visit_attributes(&def.attributes, visitor);
                for method in &def.methods {
                    visit_parameters(&method.params, visitor);
                    visit_attributes(&method.attributes, visitor);
                }
            }
            Node::Macro(def) => {
                for item in &def.contract {
                    if let MacroContractItem::Intro(intro) = item {
                        visit_macro_intro(&intro.spec, visitor);
                    }
                }
                for statement in &def.body {
                    match statement {
                        MacroStmt::ConstEval(block) | MacroStmt::Emit { block, .. } => {
                            visit_ast_nodes(&block.statements, visitor);
                        }
                        MacroStmt::Stmt(node) => visit_ast_nodes(std::slice::from_ref(node), visitor),
                    }
                }
            }
            Node::UnitFamily(def) => {
                if let Some(arithmetic) = &def.arithmetic {
                    arithmetic
                        .custom_fns
                        .iter()
                        .for_each(|function| visit_function(function, visitor));
                }
            }
            Node::CompoundUnit(def) => {
                if let Some(arithmetic) = &def.arithmetic {
                    arithmetic
                        .custom_fns
                        .iter()
                        .for_each(|function| visit_function(function, visitor));
                }
            }
            Node::Extend(def) => def.methods.iter().for_each(|method| visit_function(method, visitor)),
            Node::LiteralFunction(def) => visit_ast_nodes(&def.body.statements, visitor),
            Node::DomainBlock(def) => visit_attributes(&def.attributes, visitor),
            Node::ModDecl(def) => {
                visit_attributes(&def.attributes, visitor);
                if let Some(body) = &def.body {
                    visit_ast_nodes(body, visitor);
                }
            }
            Node::MockDecl(def) => {
                for expectation in &def.expectations {
                    visit_parameters(&expectation.params, visitor);
                    visit_ast_nodes(&expectation.body, visitor);
                }
            }
            Node::Expression(expr) => visit_expr(expr, visitor),
            Node::Let(stmt) => {
                if let Some(expr) = &stmt.value {
                    visit_expr(expr, visitor);
                }
            }
            Node::Const(stmt) => visit_expr(&stmt.value, visitor),
            Node::Static(stmt) => visit_expr(&stmt.value, visitor),
            Node::Assignment(stmt) => {
                visit_expr(&stmt.target, visitor);
                visit_expr(&stmt.value, visitor);
            }
            Node::Return(stmt) => {
                if let Some(expr) = &stmt.value {
                    visit_expr(expr, visitor);
                }
            }
            Node::Break(stmt) => {
                if let Some(expr) = &stmt.value {
                    visit_expr(expr, visitor);
                }
            }
            Node::Guard(stmt) => {
                if let Some(condition) = &stmt.condition {
                    visit_expr(condition, visitor);
                }
                visit_expr(&stmt.result, visitor);
            }
            Node::Assert(stmt) => visit_expr(&stmt.condition, visitor),
            Node::Assume(stmt) => visit_expr(&stmt.condition, visitor),
            Node::Admit(stmt) => visit_expr(&stmt.condition, visitor),
            Node::Calc(stmt) => {
                for step in &stmt.steps {
                    visit_expr(&step.expr, visitor);
                }
            }
            Node::If(stmt) => {
                visit_expr(&stmt.condition, visitor);
                visit_ast_nodes(&stmt.then_block.statements, visitor);
                for (_, condition, block) in &stmt.elif_branches {
                    visit_expr(condition, visitor);
                    visit_ast_nodes(&block.statements, visitor);
                }
                if let Some(block) = &stmt.else_block {
                    visit_ast_nodes(&block.statements, visitor);
                }
            }
            Node::Match(stmt) => {
                visit_expr(&stmt.subject, visitor);
                for arm in &stmt.arms {
                    if let Some(guard) = &arm.guard {
                        visit_expr(guard, visitor);
                    }
                    visit_ast_nodes(&arm.body.statements, visitor);
                }
            }
            Node::For(stmt) => {
                visit_expr(&stmt.iterable, visitor);
                stmt.invariants.iter().for_each(|clause| visit_clause(clause, visitor));
                visit_ast_nodes(&stmt.body.statements, visitor);
            }
            Node::While(stmt) => {
                visit_expr(&stmt.condition, visitor);
                stmt.invariants.iter().for_each(|clause| visit_clause(clause, visitor));
                visit_ast_nodes(&stmt.body.statements, visitor);
            }
            Node::Loop(stmt) => visit_ast_nodes(&stmt.body.statements, visitor),
            Node::Context(stmt) => {
                visit_expr(&stmt.context, visitor);
                visit_ast_nodes(&stmt.body.statements, visitor);
            }
            Node::With(stmt) => {
                visit_expr(&stmt.resource, visitor);
                visit_ast_nodes(&stmt.body.statements, visitor);
            }
            Node::Skip(stmt) => {
                if let SkipBody::Block(block) = &stmt.body {
                    visit_ast_nodes(&block.statements, visitor);
                }
            }
            Node::Defer(stmt) => match &stmt.body {
                DeferBody::Expr(expr) => visit_expr(expr, visitor),
                DeferBody::Block(block) => visit_ast_nodes(&block.statements, visitor),
            },
            Node::ErrDefer(stmt) => match &stmt.body {
                DeferBody::Expr(expr) => visit_expr(expr, visitor),
                DeferBody::Block(block) => visit_ast_nodes(&block.statements, visitor),
            },
            Node::InlineAsm(stmt) => {
                for constraint in &stmt.constraints {
                    if let Some(operand) = &constraint.operand {
                        visit_expr(operand, visitor);
                    }
                }
            }
            _ => {}
        }
    }
}

impl NativeProjectBuilder {
    /// Discover all .spl files in source directories.
    /// Returns ALL paths including symlink aliases (needed for import map indexing).
    /// Use `deduplicate_for_compilation` to get the unique set for actual compilation.
    pub(crate) fn discover_files(&self) -> Result<Vec<PathBuf>, String> {
        if self.config.entry_closure {
            if let Some(entry_file) = &self.entry_file {
                return self.discover_reachable_files(entry_file);
            }
            return Err("entry-closure requires --entry".to_string());
        }
        Ok(self.discover_files_full_scan())
    }

    fn discover_files_full_scan(&self) -> Vec<PathBuf> {
        let mut files = Vec::new();
        for dir in &self.source_dirs {
            if dir.is_dir() {
                collect_spl_files_recursive(dir, &mut files);
            }
        }
        if let Some(entry_file) = &self.entry_file {
            let canonical_entry = safe_canonicalize(entry_file);
            if !files.iter().any(|path| same_file_path(path, &canonical_entry)) {
                files.push(entry_file.clone());
            }
        }
        files.sort();

        files
    }

    fn discover_reachable_files(&self, entry_file: &Path) -> Result<Vec<PathBuf>, String> {
        self.discover_reachable_files_with_sources(entry_file)
            .map(|files| files.into_iter().map(|(path, _)| path).collect())
    }

    /// Discover reachable files and retain their source text so the build
    /// phase can reuse the already-read contents.
    pub(crate) fn discover_reachable_files_with_sources(
        &self,
        entry_file: &Path,
    ) -> Result<Vec<(PathBuf, String)>, String> {
        let canonical_entry = safe_canonicalize(entry_file);
        let rust_trace = native_project_rust_trace_enabled();
        if rust_trace {
            eprintln!(
                "[native-rust-trace] entry-closure discovery start entry={}",
                canonical_entry.display()
            );
        }

        // Build one resolver per source dir so imports can cross source boundaries.
        let mut resolvers: Vec<crate::module_resolver::ModuleResolver> = self
            .source_dirs
            .iter()
            .map(|dir| {
                let canonical_dir = safe_canonicalize(dir);
                crate::module_resolver::ModuleResolver::new(self.project_root.clone(), canonical_dir)
            })
            .collect();
        let project_src = self.project_root.join("src");
        if project_src.is_dir() {
            let canonical_project_src = safe_canonicalize(&project_src);
            if !self
                .source_dirs
                .iter()
                .any(|dir| safe_canonicalize(dir) == canonical_project_src)
            {
                resolvers.push(crate::module_resolver::ModuleResolver::new(
                    self.project_root.clone(),
                    canonical_project_src,
                ));
            }
        }

        // Ensure at least the effective root for the entry file is covered.
        if resolvers.is_empty() {
            let resolver_root = self.effective_source_root_for(&canonical_entry);
            resolvers.push(crate::module_resolver::ModuleResolver::new(
                self.project_root.clone(),
                resolver_root,
            ));
        }

        // Canonicalize source dirs once for the filesystem fallback.
        let mut canonical_source_dirs: Vec<PathBuf> = self.source_dirs.iter().map(|d| safe_canonicalize(d)).collect();
        if project_src.is_dir() {
            let canonical_project_src = safe_canonicalize(&project_src);
            if !canonical_source_dirs.contains(&canonical_project_src) {
                canonical_source_dirs.push(canonical_project_src);
            }
        }

        let mut queue = VecDeque::from([canonical_entry.clone()]);
        let mut queued = HashSet::from([canonical_entry.clone()]);
        let mut seen = HashSet::new();
        let mut files: Vec<(PathBuf, String)> = Vec::new();

        while let Some(path) = queue.pop_front() {
            let canonical = safe_canonicalize(&path);
            if !seen.insert(canonical.clone()) {
                continue;
            }
            if rust_trace {
                eprintln!("[native-rust-trace] discover visit {}", canonical.display());
            }

            if canonical.extension().is_some_and(|e| e == "smf") {
                continue;
            }

            let mut source = std::fs::read_to_string(&canonical)
                .map_err(|e| format!("failed to read {}: {}", canonical.display(), e))?;
            if source.contains('\r') {
                source = source.replace('\r', "");
            }
            let target_arch = super::effective_target().arch;
            source = crate::pipeline::cfg_strip::strip_inactive_cfg_arch_globals(&source, target_arch);

            let mut parser = simple_parser::Parser::new(&source);
            let mut module = parser.parse().map_err(|e| {
                let location = e
                    .span()
                    .map(|span| format!(" at {}:{}", span.line, span.column))
                    .unwrap_or_default();
                format!(
                    "failed to parse {}{} during discovery: {}",
                    canonical.display(),
                    location,
                    e
                )
            })?;
            strip_inactive_cfg_arch_fns(&mut module, target_arch);
            let mut found_deps: HashSet<PathBuf> = HashSet::new();

            // A package facade may export names implemented by sibling files.
            // Select those providers from cfg-stripped ASTs, never from text or
            // directory order, and reject ambiguous package ownership.
            if canonical.file_name().is_some_and(|name| name == "__init__.spl") {
                if module.items.iter().any(|item| {
                    matches!(item, simple_parser::ast::Node::ExportUseStmt(export)
                        if export.path.segments.is_empty() && import_target_has_glob(&export.target))
                }) {
                    return Err(format!(
                        "bare package `export *` is unsupported during native entry-closure discovery: {}",
                        canonical.display()
                    ));
                }
                let requested = bare_export_names(&module.items);
                if !requested.is_empty() {
                    let parent = canonical
                        .parent()
                        .ok_or_else(|| format!("package init has no parent: {}", canonical.display()))?;
                    let mut siblings: Vec<PathBuf> = std::fs::read_dir(parent)
                        .map_err(|e| format!("failed to read package {}: {}", parent.display(), e))?
                        .filter_map(Result::ok)
                        .map(|entry| entry.path())
                        .filter(|path| {
                            path.extension().is_some_and(|ext| ext == "spl")
                                && path
                                    .file_name()
                                    .is_some_and(|name| name != "__init__.spl" && name != "mod_stub.spl")
                        })
                        .map(|path| safe_canonicalize(&path))
                        .collect();
                    siblings.sort();
                    siblings.dedup();

                    let mut explicit_providers: BTreeMap<String, Vec<PathBuf>> =
                        requested.iter().cloned().map(|name| (name, Vec::new())).collect();
                    let mut definition_providers = explicit_providers.clone();
                    let mut facade_providers = explicit_providers.clone();
                    let mut extern_weak_providers = explicit_providers.clone();
                    let mut glob_forwarders = Vec::new();
                    for sibling in siblings {
                        let mut sibling_source = match std::fs::read_to_string(&sibling) {
                            Ok(source) => source,
                            Err(_) => continue,
                        };
                        if sibling_source.contains('\r') {
                            sibling_source = sibling_source.replace('\r', "");
                        }
                        sibling_source =
                            crate::pipeline::cfg_strip::strip_inactive_cfg_arch_globals(&sibling_source, target_arch);
                        let mut sibling_parser = simple_parser::Parser::new(&sibling_source);
                        let mut sibling_module = match sibling_parser.parse() {
                            Ok(module) => module,
                            Err(_) => continue,
                        };
                        strip_inactive_cfg_arch_fns(&mut sibling_module, target_arch);
                        let (explicit, definitions, facades, extern_weak, forwards_glob) =
                            provided_export_names(&sibling_module.items, &requested);
                        if forwards_glob {
                            glob_forwarders.push(sibling.clone());
                        }
                        for name in explicit {
                            explicit_providers.entry(name).or_default().push(sibling.clone());
                        }
                        for name in definitions {
                            definition_providers.entry(name).or_default().push(sibling.clone());
                        }
                        for name in facades {
                            facade_providers.entry(name).or_default().push(sibling.clone());
                        }
                        for name in extern_weak {
                            extern_weak_providers.entry(name).or_default().push(sibling.clone());
                        }
                    }
                    found_deps.extend(glob_forwarders);
                    for name in requested {
                        let explicit = explicit_providers.remove(&name).unwrap_or_default();
                        let definitions = definition_providers.remove(&name).unwrap_or_default();
                        let facades = facade_providers.remove(&name).unwrap_or_default();
                        let extern_weak = extern_weak_providers.remove(&name).unwrap_or_default();
                        // Tiered resolution: explicit exports beat real
                        // definitions, which beat imported facades and extern
                        // re-declarations.
                        let owners = if !explicit.is_empty() {
                            explicit
                        } else if !definitions.is_empty() {
                            definitions
                        } else if !facades.is_empty() {
                            facades
                        } else {
                            extern_weak
                        };
                        match owners.as_slice() {
                            [owner] => {
                                found_deps.insert(owner.clone());
                            }
                            [] => {}
                            _ => {
                                // Escape hatch for mid-flight source trees where two
                                // siblings genuinely define the same helper: include
                                // every candidate (over-inclusion only compiles more
                                // files) instead of failing the whole build.
                                if std::env::var("SIMPLE_AMBIGUOUS_EXPORT_ALL").map_or(false, |v| v == "1") {
                                    eprintln!(
                                        "warning: ambiguous package export `{}` in {} (including all providers): {}",
                                        name,
                                        canonical.display(),
                                        owners
                                            .iter()
                                            .map(|path| path.display().to_string())
                                            .collect::<Vec<_>>()
                                            .join(", ")
                                    );
                                    for owner in owners.iter() {
                                        found_deps.insert(owner.clone());
                                    }
                                    continue;
                                }
                                return Err(format!(
                                    "ambiguous package export `{}` in {}: {}",
                                    name,
                                    canonical.display(),
                                    owners
                                        .iter()
                                        .map(|path| path.display().to_string())
                                        .collect::<Vec<_>>()
                                        .join(", ")
                                ));
                            }
                        }
                    }
                }
            }

            // Bare exports in a package facade identify symbols but not their
            // owning sibling module. Queue only siblings that define one of
            // those symbols so unrelated files do not enter the closure.
            let bare_export_names = bare_export_names(&module.items);
            if canonical.file_name().and_then(|name| name.to_str()) == Some("__init__.spl")
                && !bare_export_names.is_empty()
            {
                if let Some(parent) = canonical.parent() {
                    if let Ok(entries) = std::fs::read_dir(parent) {
                        for entry in entries.flatten() {
                            let sibling = entry.path();
                            if sibling.extension().and_then(|ext| ext.to_str()) == Some("spl")
                                && !same_file_path(&sibling, &canonical)
                            {
                                let Ok(sibling_source) = std::fs::read_to_string(&sibling) else {
                                    continue;
                                };
                                let mut sibling_parser = simple_parser::Parser::new(&sibling_source);
                                let Ok(sibling_module) = sibling_parser.parse() else {
                                    continue;
                                };
                                if bare_export_names.iter().any(|name| {
                                    defines_top_level_name(&sibling_module.items, name)
                                        || reexports_top_level_name(&sibling_module.items, name)
                                }) {
                                    found_deps.insert(safe_canonicalize(&sibling));
                                }
                            }
                        }
                    }
                }
            }

            // Resolve each import atomically: the first resolver hit wins, and
            // the filesystem fallback runs only when every resolver misses.
            found_deps.extend(extract_reachable_module_paths(
                &module,
                &canonical,
                &mut resolvers,
                &canonical_source_dirs,
                &self.project_root,
            ));
            if rust_trace && !found_deps.is_empty() {
                eprintln!(
                    "[native-rust-trace] discover deps {} count={}",
                    canonical.display(),
                    found_deps.len()
                );
                for dep in found_deps.iter().take(8) {
                    eprintln!("  dep={}", dep.display());
                }
                if found_deps.len() > 8 {
                    eprintln!("  dep_more={}", found_deps.len() - 8);
                }
            }

            let mut found_deps: Vec<_> = found_deps.into_iter().collect();
            found_deps.sort();
            for dep in found_deps {
                if queued.insert(dep.clone()) {
                    queue.push_back(dep);
                }
            }

            files.push((canonical.clone(), source));
        }

        files.sort_by(|a, b| a.0.cmp(&b.0));
        files.dedup_by(|a, b| same_file_path(&a.0, &b.0));
        Ok(files)
    }

    /// Deduplicate files by canonical path for compilation.
    /// Returns indices into the original file list of files to actually compile.
    pub(crate) fn deduplicate_for_compilation(files: &[PathBuf]) -> Vec<usize> {
        let mut seen = std::collections::HashSet::new();
        let mut indices = Vec::new();
        for (i, path) in files.iter().enumerate() {
            let canonical = safe_canonicalize(path);
            if seen.insert(canonical) {
                indices.push(i);
            }
        }
        indices
    }
}

fn visit_reachable_nodes<'a>(
    nodes: &'a [simple_parser::ast::Node],
    visit: &mut impl FnMut(&'a simple_parser::ast::Node),
) {
    use simple_parser::ast::{DeferBody, Node, SkipBody};

    for node in nodes {
        visit(node);
        match node {
            Node::Function(function) => visit_reachable_nodes(&function.body.statements, visit),
            Node::ModDecl(module) => {
                if let Some(body) = &module.body {
                    visit_reachable_nodes(body, visit);
                }
            }
            Node::Class(class) => {
                for method in &class.methods {
                    visit_reachable_nodes(&method.body.statements, visit);
                }
            }
            Node::Struct(structure) => {
                for method in &structure.methods {
                    visit_reachable_nodes(&method.body.statements, visit);
                }
            }
            Node::Enum(enumeration) => {
                for method in &enumeration.methods {
                    visit_reachable_nodes(&method.body.statements, visit);
                }
            }
            Node::Impl(implementation) => {
                for method in &implementation.methods {
                    visit_reachable_nodes(&method.body.statements, visit);
                }
            }
            Node::Trait(trait_def) => {
                for method in &trait_def.methods {
                    visit_reachable_nodes(&method.body.statements, visit);
                }
            }
            Node::Mixin(mixin) => {
                for method in &mixin.methods {
                    visit_reachable_nodes(&method.body.statements, visit);
                }
            }
            Node::Actor(actor) => {
                for method in &actor.methods {
                    visit_reachable_nodes(&method.body.statements, visit);
                }
            }
            Node::Extend(extension) => {
                for method in &extension.methods {
                    visit_reachable_nodes(&method.body.statements, visit);
                }
            }
            Node::LiteralFunction(function) => visit_reachable_nodes(&function.body.statements, visit),
            Node::If(stmt) => {
                visit_reachable_nodes(&stmt.then_block.statements, visit);
                for (_, _, block) in &stmt.elif_branches {
                    visit_reachable_nodes(&block.statements, visit);
                }
                if let Some(block) = &stmt.else_block {
                    visit_reachable_nodes(&block.statements, visit);
                }
            }
            Node::While(stmt) => visit_reachable_nodes(&stmt.body.statements, visit),
            Node::For(stmt) => visit_reachable_nodes(&stmt.body.statements, visit),
            Node::Loop(stmt) => visit_reachable_nodes(&stmt.body.statements, visit),
            Node::Context(stmt) => visit_reachable_nodes(&stmt.body.statements, visit),
            Node::With(stmt) => visit_reachable_nodes(&stmt.body.statements, visit),
            Node::Match(stmt) => {
                for arm in &stmt.arms {
                    visit_reachable_nodes(&arm.body.statements, visit);
                }
            }
            Node::Defer(stmt) => {
                if let DeferBody::Block(block) = &stmt.body {
                    visit_reachable_nodes(&block.statements, visit);
                }
            }
            Node::ErrDefer(stmt) => {
                if let DeferBody::Block(block) = &stmt.body {
                    visit_reachable_nodes(&block.statements, visit);
                }
            }
            Node::Skip(stmt) => {
                if let SkipBody::Block(block) = &stmt.body {
                    visit_reachable_nodes(&block.statements, visit);
                }
            }
            _ => {}
        }
    }
}

fn defines_top_level_name(items: &[simple_parser::ast::Node], name: &str) -> bool {
    use simple_parser::ast::{Node, Pattern};

    items.iter().any(|item| match item {
        Node::Function(def) => def.name == name,
        Node::Struct(def) => def.name == name,
        Node::Class(def) => def.name == name,
        Node::Enum(def) => def.name == name,
        Node::Trait(def) => def.name == name,
        Node::Mixin(def) => def.name == name,
        Node::Actor(def) => def.name == name,
        Node::TypeAlias(def) => def.name == name,
        Node::ClassAlias(def) => def.name == name,
        Node::FunctionAlias(def) => def.name == name,
        Node::Extern(def) => def.name == name,
        Node::ExternClass(def) => def.name == name,
        Node::Macro(def) => def.name == name,
        Node::Bitfield(def) => def.name == name,
        Node::Newtype(def) => def.name == name,
        Node::Unit(def) => def.name == name,
        Node::UnitFamily(def) => def.name == name,
        Node::CompoundUnit(def) => def.name == name,
        Node::HandlePool(def) => def.type_name == name,
        Node::Const(def) => def.name == name,
        Node::Static(def) => def.name == name,
        Node::Let(def) => matches!(&def.pattern, Pattern::Identifier(identifier) if identifier == name),
        _ => false,
    })
}

fn reexports_top_level_name(items: &[simple_parser::ast::Node], name: &str) -> bool {
    use simple_parser::ast::{ExportUseStmt, ImportTarget, Node};

    fn target_exports_name(target: &ImportTarget, name: &str) -> bool {
        match target {
            ImportTarget::Glob => true,
            ImportTarget::Single(exported) => exported == name,
            ImportTarget::Aliased { alias, .. } => alias == name,
            ImportTarget::Group(targets) => targets.iter().any(|target| target_exports_name(target, name)),
        }
    }

    items.iter().any(|item| {
        matches!(
            item,
            Node::ExportUseStmt(ExportUseStmt { path, target, .. })
                if !path.segments.is_empty() && target_exports_name(target, name)
        )
    })
}

pub(crate) fn extract_reachable_module_paths(
    module: &simple_parser::ast::Module,
    from_file: &Path,
    resolvers: &mut [crate::module_resolver::ModuleResolver],
    fallback_roots: &[PathBuf],
    project_root: &Path,
) -> Vec<PathBuf> {
    use simple_parser::ast::{
        AutoImportStmt, CommonUseStmt, ExportUseStmt, ImportTarget, ModDecl, ModulePath, MultiUse, Node, UseStmt,
    };

    fn resolve_candidate(
        resolvers: &mut [crate::module_resolver::ModuleResolver],
        fallback_roots: &[PathBuf],
        project_root: &Path,
        from_file: &Path,
        path: &ModulePath,
        target: Option<&ImportTarget>,
    ) -> Option<PathBuf> {
        for resolver in resolvers {
            match target {
                Some(ImportTarget::Single(name)) | Some(ImportTarget::Aliased { name, .. }) => {
                    let mut module_segments = path.segments.clone();
                    module_segments.push(name.clone());
                    let module_path = ModulePath::new(module_segments);
                    if let Ok(resolved) = resolver.resolve(&module_path, from_file) {
                        return Some(safe_canonicalize(&resolved.path));
                    }
                }
                _ => {}
            }
            if let Ok(resolved) = resolver.resolve(path, from_file) {
                return Some(safe_canonicalize(&resolved.path));
            }
        }

        let mut segment_lists = Vec::new();
        if let Some(ImportTarget::Single(name)) | Some(ImportTarget::Aliased { name, .. }) = target {
            let mut segments = path.segments.clone();
            segments.push(name.clone());
            segment_lists.push(segments);
        }
        segment_lists.push(path.segments.clone());

        for segments in segment_lists {
            if segments.is_empty() {
                continue;
            }
            if segments[0] == "lib" && segments.len() > 1 {
                return find_module_file(&project_root.join("src/lib"), &segments[1..]);
            }
            for root in fallback_roots {
                let root_name = root.file_name().and_then(|name| name.to_str()).unwrap_or("");
                if segments[0] == root_name {
                    if let Some(found) = find_module_file(root, &segments[1..]) {
                        return Some(found);
                    }
                }
                if let Some(found) = find_module_file(root, &segments) {
                    return Some(found);
                }
            }
        }
        None
    }

    fn find_module_file(root: &Path, segments: &[String]) -> Option<PathBuf> {
        if segments.is_empty() {
            return None;
        }
        let rel_path: PathBuf = segments.iter().collect();
        for candidate in [
            root.join(&rel_path).with_extension("spl"),
            root.join(&rel_path).join("mod.spl"),
            root.join(&rel_path).join("__init__.spl"),
        ] {
            if candidate.is_file() {
                return Some(safe_canonicalize(&candidate));
            }
        }
        None
    }

    fn push_dep(
        deps: &mut Vec<PathBuf>,
        resolvers: &mut [crate::module_resolver::ModuleResolver],
        fallback_roots: &[PathBuf],
        project_root: &Path,
        from_file: &Path,
        path: &ModulePath,
        target: Option<&ImportTarget>,
    ) {
        if let Some(resolved) = resolve_candidate(resolvers, fallback_roots, project_root, from_file, path, target) {
            if !deps.iter().any(|existing| same_file_path(existing, &resolved)) {
                deps.push(resolved);
            }
        }
    }

    let mut deps = Vec::new();
    visit_ast_nodes(&module.items, &mut |item| match item {
        Node::UseStmt(UseStmt { path, target, .. }) => push_dep(
            &mut deps,
            resolvers,
            fallback_roots,
            project_root,
            from_file,
            path,
            Some(target),
        ),
        Node::CommonUseStmt(CommonUseStmt { path, target, .. }) => push_dep(
            &mut deps,
            resolvers,
            fallback_roots,
            project_root,
            from_file,
            path,
            Some(target),
        ),
        Node::ExportUseStmt(ExportUseStmt { path, target, .. }) => push_dep(
            &mut deps,
            resolvers,
            fallback_roots,
            project_root,
            from_file,
            path,
            Some(target),
        ),
        Node::MultiUse(MultiUse { imports, .. }) => {
            for (path, target) in imports {
                push_dep(
                    &mut deps,
                    resolvers,
                    fallback_roots,
                    project_root,
                    from_file,
                    path,
                    Some(target),
                );
            }
        }
        Node::AutoImportStmt(AutoImportStmt { path, .. }) => push_dep(
            &mut deps,
            resolvers,
            fallback_roots,
            project_root,
            from_file,
            path,
            None,
        ),
        Node::ModDecl(ModDecl { name, body, .. }) if body.is_none() => {
            let path = ModulePath::new(vec![name.clone()]);
            push_dep(
                &mut deps,
                resolvers,
                fallback_roots,
                project_root,
                from_file,
                &path,
                None,
            );
        }
        _ => {}
    });
    deps
}
