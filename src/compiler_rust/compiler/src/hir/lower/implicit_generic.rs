//! Stage 1 of implicit generics for unannotated parameters and returns.
//!
//! `fn f(x): x` declares no types. It is NOT `any`: an unannotated parameter is
//! a fresh type variable, generalized at the definition and instantiated at each
//! call site, so `f([1.5])` is `[f64]` and `f(3)` is `i64`. The seed erases
//! generic bodies to one tagged-value function, so the instantiation happens at
//! the call: the result is retyped to the instantiated type (and a numeric
//! scalar is decoded out of its tagged word with a cast).
//!
//! Stage 1 infers only the identity shape (the body is exactly the parameter).
//! Everything else stays for the staged HM plan; where a result cannot be
//! inferred, safe code is rejected at the typed use instead of computing on a
//! tagged word (`any` is allowed only inside `unsafe` and in script mode).
//! doc/08_tracking/bug/seed_value_join_any_option_disagree_wrong_values_2026-11-27.md

use simple_parser::ast::{self, Expr, Node};

use super::context::FunctionContext;
use super::error::{LowerError, LowerResult};
use super::lowerer::{GenericIdentityParamSpec, Lowerer};
use crate::hir::types::{HirExpr, HirExprKind, HirStmt, HirType, TypeId};

use crate::pipeline::script_detection::SCRIPT_ENTRY_ATTR;

fn is_numeric(ty: TypeId) -> bool {
    matches!(
        ty,
        TypeId::I8
            | TypeId::I16
            | TypeId::I32
            | TypeId::I64
            | TypeId::U8
            | TypeId::U16
            | TypeId::U32
            | TypeId::U64
            | TypeId::F32
            | TypeId::F64
    )
}

impl Lowerer {
    /// `fn f(.., x, ..): x` (or `return x`) with `x` unannotated or typed by a
    /// generic parameter, and no return annotation: the result type is the
    /// type variable of `x`.
    pub(super) fn implicit_identity_param_spec(f: &ast::FunctionDef) -> Option<GenericIdentityParamSpec> {
        if f.return_type.is_some() {
            return None;
        }
        let [only] = f.body.statements.as_slice() else {
            return None;
        };
        let returned = match only {
            Node::Expression(Expr::Identifier(name)) => name,
            Node::Return(ret) => match &ret.value {
                Some(Expr::Identifier(name)) => name,
                _ => return None,
            },
            _ => return None,
        };
        let (index, param) = f
            .params
            .iter()
            .enumerate()
            .find(|(_, p)| &p.name == returned && p.name != "self")?;
        let is_type_variable = match &param.ty {
            None => true,
            Some(ast::Type::Simple(name)) => f.generic_params.iter().any(|g| g == name),
            Some(_) => false,
        };
        if !is_type_variable || param.variadic {
            return None;
        }
        Some(GenericIdentityParamSpec {
            index,
            name: param.name.clone(),
            generic_param_pos: None,
            same_type_params: Vec::new(),
        })
    }

    /// Whether a type variable may be instantiated to `ty`: a known type with
    /// no `any` inside (`[any]` is not an instantiation).
    pub(super) fn is_instantiable_type(&self, ty: TypeId) -> bool {
        if matches!(
            ty,
            TypeId::ANY | TypeId::VOID | TypeId::NIL | TypeId::BOOL | TypeId::CHAR
        ) {
            // bool/char travel as tagged words with no cast that decodes them;
            // stage 1 leaves them uninstantiated rather than mistyping the word.
            return false;
        }
        match self.module.types.get(ty) {
            None | Some(HirType::Any) | Some(HirType::Function { .. }) => false,
            Some(HirType::Array { element, .. }) => self.is_instantiable_type(*element),
            Some(HirType::Tuple(items)) => items.iter().all(|item| self.is_instantiable_type(*item)),
            Some(HirType::Dict { key, value }) => self.is_instantiable_type(*key) && self.is_instantiable_type(*value),
            Some(_) => true,
        }
    }

    /// Give an erased generic call its instantiated type. The callee returns a
    /// tagged word, so a numeric instantiation is decoded with a cast; every
    /// other instantiable type is the same heap word either way.
    pub(super) fn instantiate_generic_call(&self, call: HirExpr, instantiated: TypeId) -> HirExpr {
        if call.ty == instantiated || !is_numeric(instantiated) {
            return HirExpr {
                ty: instantiated,
                ..call
            };
        }
        HirExpr {
            kind: HirExprKind::Cast {
                // The erased callee returns a tagged word whatever the
                // (possibly not yet lowered) declaration says.
                expr: Box::new(HirExpr {
                    ty: TypeId::ANY,
                    ..call
                }),
                target: instantiated,
            },
            ty: instantiated,
        }
    }

    /// Whether the unit's entry is a script: its `main` was synthesized from
    /// top-level statements (`wrap_entry_script_as_main`, the spec entry), or,
    /// on the run lane only, it has executable top-level statements and no
    /// `main` of its own (that lane lowers such a unit and then hands it to
    /// the interpreter).
    pub(super) fn is_script_entry(&self, module: &ast::Module) -> bool {
        let mut has_entry_main = false;
        let mut has_statement = false;
        for item in &module.items {
            match item {
                Node::Function(f) if f.attributes.iter().any(|a| a.name == SCRIPT_ENTRY_ATTR) => return true,
                Node::Function(f) if f.name == "main" => {
                    has_entry_main |= Self::flatten_owner_of(f.attributes.iter().map(|a| a.name.as_str())).is_none();
                }
                Node::Expression(_)
                | Node::Assignment(_)
                | Node::If(_)
                | Node::Match(_)
                | Node::For(_)
                | Node::While(_)
                | Node::Loop(_)
                | Node::With(_)
                | Node::Context(_) => has_statement = true,
                _ => {}
            }
        }
        self.mainless_unit_is_script && has_statement && !has_entry_main
    }

    /// `any` is permitted where the code under lowering is inside `unsafe:`
    /// or belongs to a script entry (top-level statements; not a module).
    fn any_is_permitted(&self, ctx: &FunctionContext) -> bool {
        ctx.unsafe_depth > 0 || (self.entry_is_script && self.current_function_owner.is_none())
    }

    /// Script file kinds (`.shs`, `.sscript`), as the driver classifies them.
    pub(super) fn is_script_file(&self) -> bool {
        self.current_file
            .as_ref()
            .and_then(|path| path.extension())
            .and_then(|ext| ext.to_str())
            .is_some_and(|ext| matches!(ext, "shs" | "sscript"))
    }

    /// The origin of `expr` when its type could not be inferred: an
    /// unannotated parameter, a local bound from one, or a call to an
    /// unannotated function that stage 1 could not instantiate. The second
    /// item names a callee whose body is not lowered yet, so whether the call
    /// yields a value at all is still unknown.
    fn uninferred_origin(&self, expr: &HirExpr, ctx: &FunctionContext) -> Option<(String, Option<String>)> {
        // A call to a function declared further down is typed `()` until its
        // body is lowered, so `()` is as untyped here as `any`.
        if let HirExprKind::Local(index) = &expr.kind {
            return ctx.uninferred_locals.get(index).cloned();
        }
        let forward_call = expr.ty == TypeId::VOID && matches!(expr.kind, HirExprKind::Call { .. });
        if expr.ty != TypeId::ANY && !forward_call {
            return None;
        }
        match &expr.kind {
            HirExprKind::Block(stmts) => match stmts.last() {
                Some(HirStmt::Expr(tail)) => self.uninferred_origin(tail, ctx),
                _ => None,
            },
            HirExprKind::Call { func, .. } => match &func.kind {
                HirExprKind::Global(symbol) => {
                    let origin = format!("the result of unannotated function `{symbol}`");
                    match self.unannotated_return_fns.get(symbol)? {
                        Some(false) => None,
                        Some(true) => Some((origin, None)),
                        None => Some((origin, Some(symbol.clone()))),
                    }
                }
                _ => None,
            },
            // A value read out of an uninferred one is as untyped as its source.
            HirExprKind::MethodCall { receiver, .. } | HirExprKind::FieldAccess { receiver, .. } => {
                self.uninferred_origin(receiver, ctx)
            }
            HirExprKind::BuiltinCall { args, .. } => args.first().and_then(|arg| self.uninferred_origin(arg, ctx)),
            HirExprKind::Unary { operand, .. } => self.uninferred_origin(operand, ctx),
            HirExprKind::Binary { left, right, .. } => {
                self.uninferred_origin(left, ctx).or_else(|| self.uninferred_origin(right, ctx))
            }
            _ => None,
        }
    }

    /// A body whose only result is a unit-typed tail (`print(msg)`) is a
    /// procedure even though its erased return slot is a tagged word.
    pub(super) fn body_ends_in_unit(body: &[HirStmt]) -> bool {
        let returns_value = body.iter().any(|stmt| matches!(stmt, HirStmt::Return(Some(_))));
        !returns_value && matches!(body.last(), Some(HirStmt::Expr(tail)) if tail.ty == TypeId::NIL)
    }

    /// Record an unannotated `val`/`var` bound from an uninferred value.
    pub(super) fn bind_uninferred_local(&self, local: usize, value: Option<&HirExpr>, ctx: &mut FunctionContext) {
        if let Some(origin) = value.and_then(|v| self.uninferred_origin(v, ctx)) {
            ctx.uninferred_locals.insert(local, origin);
        }
    }

    /// Reject an uninferred value at a typed use.
    pub(super) fn reject_uninferred(&mut self, expr: &HirExpr, usage: &str, ctx: &FunctionContext) -> LowerResult<()> {
        if self.any_is_permitted(ctx) {
            return Ok(());
        }
        let Some((origin, pending_callee)) = self.uninferred_origin(expr, ctx) else {
            return Ok(());
        };
        let function = self.current_function_name.clone().unwrap_or_default();
        let error = LowerError::UninferredType {
            origin,
            usage: usage.to_string(),
            function,
        };
        // Every site of the unit is reported together once all bodies are
        // lowered (`judge_pending_uninferred_uses`).
        self.pending_uninferred_uses.push((pending_callee, error));
        Ok(())
    }

    /// Once every body is lowered: report every recorded use and fail with the
    /// first. A use of a forward-referenced callee counts unless the callee
    /// turned out to be a procedure.
    pub(crate) fn judge_pending_uninferred_uses(&mut self) -> LowerResult<()> {
        let mut first = None;
        for (callee, error) in std::mem::take(&mut self.pending_uninferred_uses) {
            let is_value = match &callee {
                Some(callee) => self.unannotated_return_fns.get(callee) == Some(&Some(true)),
                None => true,
            };
            if is_value {
                eprintln!("error[uninferred-any]: {error}");
                first.get_or_insert(error);
            }
        }
        first.map_or(Ok(()), Err)
    }

    /// Arithmetic, bitwise and ordered comparison need operand types.
    pub(super) fn reject_uninferred_operands(
        &mut self,
        op: &ast::BinOp,
        left: &HirExpr,
        right: &HirExpr,
        ctx: &FunctionContext,
    ) -> LowerResult<()> {
        use ast::BinOp::*;
        if !matches!(
            op,
            Add | Sub
                | Mul
                | Div
                | Mod
                | Pow
                | BitAnd
                | BitOr
                | BitXor
                | ShiftLeft
                | ShiftRight
                | Lt
                | Gt
                | LtEq
                | GtEq
        ) {
            return Ok(());
        }
        self.reject_uninferred(left, "arithmetic", ctx)?;
        self.reject_uninferred(right, "arithmetic", ctx)
    }

    /// An uninferred arm cannot be joined with a typed sibling: the join would
    /// hold a tagged word in one arm and a typed value in the other.
    pub(super) fn reject_uninferred_join(
        &mut self,
        then_arm: &HirExpr,
        else_arm: Option<&HirExpr>,
        ctx: &FunctionContext,
    ) -> LowerResult<()> {
        let Some(else_arm) = else_arm else {
            return Ok(());
        };
        let typed = |arm: &HirExpr| !matches!(arm.ty, TypeId::ANY | TypeId::VOID | TypeId::NIL);
        if typed(else_arm) {
            self.reject_uninferred(then_arm, "an if/match arm joined with a typed arm", ctx)?;
        }
        if typed(then_arm) {
            self.reject_uninferred(else_arm, "an if/match arm joined with a typed arm", ctx)?;
        }
        Ok(())
    }
}
