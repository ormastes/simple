//! Lexical unsafe enforcement for raw foreign calls in the Rust seed.
//!
//! This pass is intentionally HIR-only. It adds no target-runtime branch,
//! lookup, allocation, or wrapper and runs before MIR erases `UnsafeBlock`.

use crate::hir::{HirExpr, HirExprKind, HirModule, HirStmt};
use std::sync::OnceLock;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsafeFfiViolation {
    pub function: String,
    pub callee: String,
}

/// Return the first direct call to a module-local extern function that is not
/// enclosed by a lexical `unsafe` block. Fail-fast admission bounds memory to
/// one diagnostic even for a large legacy module.
pub fn check_unsafe_ffi(module: &HirModule) -> Vec<UnsafeFfiViolation> {
    let mut out = Vec::new();
    for function in &module.functions {
        check_stmts(module, &function.name, &function.body, false, &mut out);
        if !out.is_empty() {
            break;
        }
    }
    out
}

/// The seed mirrors the pure compiler's settled profile policy: critical and
/// verified deny unsafe FFI, lower profiles remain migration diagnostics.
/// Cached once so module count cannot turn profile lookup into a build-time
/// hot-path regression.
pub fn unsafe_ffi_deny_enabled() -> bool {
    static DENY: OnceLock<bool> = OnceLock::new();
    *DENY.get_or_init(|| {
        matches!(
            std::env::var("SIMPLE_SAFETY_PROFILE")
                .unwrap_or_default()
                .trim()
                .to_ascii_lowercase()
                .as_str(),
            "critical" | "verified" | "mission-critical" | "mission_critical"
        )
    })
}

#[inline]
fn is_raw_ffi_name(module: &HirModule, name: &str) -> bool {
    // Imported raw providers are not present in this module's local extern
    // table. Preserve their FFI identity without a registry or hash lookup.
    name.starts_with("rt_") || name.starts_with("spl_") || module.extern_fn_names.contains(name)
}

fn check_stmts(
    module: &HirModule,
    function: &str,
    stmts: &[HirStmt],
    in_unsafe: bool,
    out: &mut Vec<UnsafeFfiViolation>,
) {
    for stmt in stmts {
        if !out.is_empty() {
            return;
        }
        match stmt {
            HirStmt::Let { value, .. } => {
                if let Some(value) = value {
                    check_expr(module, function, value, in_unsafe, out);
                }
            }
            HirStmt::Assign { target, value } => {
                check_expr(module, function, target, in_unsafe, out);
                check_expr(module, function, value, in_unsafe, out);
            }
            HirStmt::Return(value) => {
                if let Some(value) = value {
                    check_expr(module, function, value, in_unsafe, out);
                }
            }
            HirStmt::Expr(expr) => check_expr(module, function, expr, in_unsafe, out),
            HirStmt::If {
                condition,
                then_block,
                else_block,
                ..
            } => {
                check_expr(module, function, condition, in_unsafe, out);
                check_stmts(module, function, then_block, in_unsafe, out);
                if let Some(block) = else_block {
                    check_stmts(module, function, block, in_unsafe, out);
                }
            }
            HirStmt::While {
                condition,
                body,
                invariants,
                ..
            } => {
                check_expr(module, function, condition, in_unsafe, out);
                for clause in invariants {
                    check_expr(module, function, &clause.condition, in_unsafe, out);
                }
                check_stmts(module, function, body, in_unsafe, out);
            }
            HirStmt::For {
                iterable,
                body,
                invariants,
                ..
            } => {
                check_expr(module, function, iterable, in_unsafe, out);
                for clause in invariants {
                    check_expr(module, function, &clause.condition, in_unsafe, out);
                }
                check_stmts(module, function, body, in_unsafe, out);
            }
            HirStmt::Loop { body, .. } | HirStmt::Defer { body } => {
                check_stmts(module, function, body, in_unsafe, out);
            }
            HirStmt::Assert { condition, .. }
            | HirStmt::Assume { condition, .. }
            | HirStmt::Admit { condition, .. } => {
                check_expr(module, function, condition, in_unsafe, out);
            }
            HirStmt::Calc { steps } => {
                for step in steps {
                    check_expr(module, function, &step.expr, in_unsafe, out);
                }
            }
            HirStmt::Break | HirStmt::Continue | HirStmt::ProofHint { .. } | HirStmt::InlineAsm { .. } => {}
        }
    }
}

fn check_expr(module: &HirModule, function: &str, expr: &HirExpr, in_unsafe: bool, out: &mut Vec<UnsafeFfiViolation>) {
    if !out.is_empty() {
        return;
    }
    match &expr.kind {
        HirExprKind::Call { func, args } => {
            if !in_unsafe {
                if let HirExprKind::Global(name) = &func.kind {
                    if is_raw_ffi_name(module, name) {
                        out.push(UnsafeFfiViolation {
                            function: function.to_owned(),
                            callee: name.clone(),
                        });
                    }
                }
            }
            check_expr(module, function, func, in_unsafe, out);
            for arg in args {
                check_expr(module, function, arg, in_unsafe, out);
            }
        }
        HirExprKind::UnsafeBlock(stmts) => check_stmts(module, function, stmts, true, out),
        HirExprKind::Block(stmts) => check_stmts(module, function, stmts, in_unsafe, out),
        HirExprKind::Binary { left, right, .. } => {
            check_expr(module, function, left, in_unsafe, out);
            check_expr(module, function, right, in_unsafe, out);
        }
        HirExprKind::Unary { operand, .. }
        | HirExprKind::Ref(operand)
        | HirExprKind::Deref(operand)
        | HirExprKind::Cast { expr: operand, .. }
        | HirExprKind::Yield(operand)
        | HirExprKind::GeneratorCreate { body: operand }
        | HirExprKind::FutureCreate { body: operand }
        | HirExprKind::Await(operand)
        | HirExprKind::ActorSpawn { body: operand }
        | HirExprKind::ContractOld(operand) => check_expr(module, function, operand, in_unsafe, out),
        HirExprKind::PointerNew { value, .. } => check_expr(module, function, value, in_unsafe, out),
        HirExprKind::MethodCall { receiver, args, .. } => {
            check_expr(module, function, receiver, in_unsafe, out);
            for arg in args {
                check_expr(module, function, arg, in_unsafe, out);
            }
        }
        HirExprKind::FieldAccess { receiver, .. } => check_expr(module, function, receiver, in_unsafe, out),
        HirExprKind::Index { receiver, index } => {
            check_expr(module, function, receiver, in_unsafe, out);
            check_expr(module, function, index, in_unsafe, out);
        }
        HirExprKind::Tuple(values) | HirExprKind::Array(values) | HirExprKind::VecLiteral(values) => {
            for value in values {
                check_expr(module, function, value, in_unsafe, out);
            }
        }
        HirExprKind::ArrayRepeat { value, count } => {
            check_expr(module, function, value, in_unsafe, out);
            check_expr(module, function, count, in_unsafe, out);
        }
        HirExprKind::StructInit { fields, .. } => {
            for field in fields {
                check_expr(module, function, field, in_unsafe, out);
            }
        }
        HirExprKind::Dict(entries) => {
            for (key, value) in entries {
                check_expr(module, function, key, in_unsafe, out);
                check_expr(module, function, value, in_unsafe, out);
            }
        }
        HirExprKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            check_expr(module, function, condition, in_unsafe, out);
            check_expr(module, function, then_branch, in_unsafe, out);
            if let Some(branch) = else_branch {
                check_expr(module, function, branch, in_unsafe, out);
            }
        }
        HirExprKind::Lambda { body, .. } => check_expr(module, function, body, in_unsafe, out),
        HirExprKind::BuiltinCall { args, .. } | HirExprKind::GpuIntrinsic { args, .. } => {
            for arg in args {
                check_expr(module, function, arg, in_unsafe, out);
            }
        }
        HirExprKind::LetIn { value, body, .. } => {
            check_expr(module, function, value, in_unsafe, out);
            check_expr(module, function, body, in_unsafe, out);
        }
        HirExprKind::NeighborAccess { array, .. } => check_expr(module, function, array, in_unsafe, out),
        HirExprKind::Integer(_)
        | HirExprKind::Float(_)
        | HirExprKind::String(_)
        | HirExprKind::Bool(_)
        | HirExprKind::Nil
        | HirExprKind::Local(_)
        | HirExprKind::Global(_)
        | HirExprKind::ContractResult => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::lower::Lowerer;
    use simple_parser::Parser;

    fn lower(source: &str) -> HirModule {
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("parse");
        Lowerer::new().lower_module(&module).expect("lower")
    }

    #[test]
    fn rejects_raw_extern_call_outside_unsafe() {
        let module = lower("extern fn rt_probe() -> i64\nfn run() -> i64:\n    rt_probe()\n");
        let violations = check_unsafe_ffi(&module);
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].callee, "rt_probe");
    }

    #[test]
    fn accepts_raw_extern_call_inside_unsafe() {
        let module = lower(
            "extern fn rt_probe() -> i64\nfn run() -> i64:\n    unsafe(capabilities: [ffi]):\n        rt_probe()\n",
        );
        assert!(check_unsafe_ffi(&module).is_empty());
    }

    #[test]
    fn rejects_imported_style_rt_call_without_local_extern_declaration() {
        let module = lower("fn rt_imported_probe() -> i64:\n    1\nfn run() -> i64:\n    rt_imported_probe()\n");
        let violations = check_unsafe_ffi(&module);
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].callee, "rt_imported_probe");
    }

    #[test]
    fn accepts_imported_style_rt_call_inside_unsafe() {
        let module = lower(
            "fn rt_imported_probe() -> i64:\n    1\nfn run() -> i64:\n    unsafe(capabilities: [ffi]):\n        rt_imported_probe()\n",
        );
        assert!(check_unsafe_ffi(&module).is_empty());
    }
}
