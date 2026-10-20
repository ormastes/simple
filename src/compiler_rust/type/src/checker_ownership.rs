// No-GC ownership-sigil rules (doc/05_design/language/misc/memory.md).
//
// `&T` unique owner, `*T` shared Rc owner, `-T` weak observer. Every check
// here is a no-op unless `nogc_strict` (opt-in `@no_gc(strict)` or
// `SIMPLE_NOGC_STRICT=1`) is set, so default-mode programs see no change.
//
// Conversions (memory.md + plan §3.0 proposal, see PR body):
//   &T -> *T   explicit only: share(move u)
//   *T -> &T   forbidden
//   *T -> -T   weak_of(s)
//   -T -> *T   w.upgrade() -> Option<*T>

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum SigilKind {
    Unique,
    Shared,
    Weak,
}

fn sigil_kind(ty: &Type) -> Option<SigilKind> {
    match ty {
        Type::Unique(_) => Some(SigilKind::Unique),
        Type::Shared(_) => Some(SigilKind::Shared),
        Type::Weak(_) => Some(SigilKind::Weak),
        _ => None,
    }
}

fn sigil_spelling(kind: SigilKind) -> &'static str {
    match kind {
        SigilKind::Unique => "&T (unique)",
        SigilKind::Shared => "*T (shared)",
        SigilKind::Weak => "-T (weak)",
    }
}

fn conversion_hint(from: SigilKind, to: SigilKind) -> &'static str {
    match (from, to) {
        (SigilKind::Unique, SigilKind::Shared) => "unique -> shared must be explicit: share(move x)",
        (SigilKind::Shared, SigilKind::Unique) => "shared -> unique is forbidden",
        (SigilKind::Shared, SigilKind::Weak) => "make a weak reference with weak_of(s)",
        (SigilKind::Weak, SigilKind::Shared) => "upgrade first: w.upgrade() returns Option<*T>",
        (SigilKind::Unique, SigilKind::Weak) => "a weak reference observes a *T; share(move x) first",
        (SigilKind::Weak, SigilKind::Unique) => "a weak reference can never become unique",
        _ => "",
    }
}

impl TypeChecker {
    /// Strict-mode check that a value of type `found` may flow into a slot
    /// declared as `expected` (`what` names the slot for the diagnostic).
    pub(crate) fn check_ownership_flow(&self, found: &Type, expected: &Type, what: &str) -> Result<(), TypeError> {
        if !self.nogc_strict {
            return Ok(());
        }
        let found = self.resolve(found);
        let expected = self.resolve(expected);
        if let (Type::Optional(f), Type::Optional(e)) = (&found, &expected) {
            return self.check_ownership_flow(f, e, what);
        }
        match (sigil_kind(&found), sigil_kind(&expected)) {
            (Some(a), Some(b)) if a == b => Ok(()),
            (Some(a), Some(b)) => Err(TypeError::Ownership(format!(
                "{what}: cannot use {} where {} is required; {}",
                sigil_spelling(a),
                sigil_spelling(b),
                conversion_hint(a, b)
            ))),
            (Some(a), None) => match expected {
                Type::Var(_) | Type::TypeParam(_) | Type::Nil => Ok(()),
                _ => Err(TypeError::Ownership(format!(
                    "{what}: {} does not implicitly convert to a plain value",
                    sigil_spelling(a)
                ))),
            },
            (None, Some(b)) => match found {
                // Unknown/inferred value or a fresh constructor result.
                Type::Var(_) | Type::TypeParam(_) => Ok(()),
                // nil-outside-unsafe is a later stage (NIL-UNSAFE-001).
                Type::Nil => Ok(()),
                Type::Named(ref name) if b == SigilKind::Unique && self.class_names.contains(name) => Ok(()),
                Type::Optional(_) => Err(TypeError::Ownership(format!(
                    "{what}: an Option is not {}; match on it first",
                    sigil_spelling(b)
                ))),
                _ => Err(TypeError::Ownership(format!(
                    "{what}: a plain value does not implicitly become {}",
                    sigil_spelling(b)
                ))),
            },
            (None, None) => Ok(()),
        }
    }

    /// `share(move u)`: consume a unique owner into a shared one.
    pub(crate) fn infer_share_call(&mut self, args: &[simple_parser::ast::Argument]) -> Result<Type, TypeError> {
        let arg = match args {
            [single] => &single.value,
            _ => return Ok(self.fresh_var()),
        };
        let is_move = matches!(arg, Expr::Unary { op: simple_parser::ast::UnaryOp::Move, .. });
        let arg_ty = self.infer_expr(arg)?;
        match self.resolve(&arg_ty) {
            Type::Unique(inner) => {
                if self.nogc_strict && !is_move {
                    return Err(TypeError::Ownership(
                        "share(x): unique -> shared consumes the owner and must be explicit: share(move x)".into(),
                    ));
                }
                Ok(Type::Shared(inner))
            }
            Type::Var(_) => Ok(Type::Shared(Box::new(self.fresh_var()))),
            other => {
                if self.nogc_strict {
                    let got = sigil_kind(&other).map(sigil_spelling).unwrap_or("a plain value");
                    return Err(TypeError::Ownership(format!(
                        "share(x) takes a unique owner &T, got {got}"
                    )));
                }
                Ok(self.fresh_var())
            }
        }
    }

    /// `weak_of(s)`: observe a shared owner without keeping it alive.
    pub(crate) fn infer_weak_of_call(&mut self, args: &[simple_parser::ast::Argument]) -> Result<Type, TypeError> {
        let arg = match args {
            [single] => &single.value,
            _ => return Ok(self.fresh_var()),
        };
        let arg_ty = self.infer_expr(arg)?;
        match self.resolve(&arg_ty) {
            Type::Shared(inner) => Ok(Type::Weak(inner)),
            Type::Var(_) => Ok(Type::Weak(Box::new(self.fresh_var()))),
            other => {
                if self.nogc_strict {
                    let got = sigil_kind(&other).map(sigil_spelling).unwrap_or("a plain value");
                    return Err(TypeError::Ownership(format!(
                        "weak_of(x) takes a shared owner *T, got {got}"
                    )));
                }
                Ok(self.fresh_var())
            }
        }
    }

    /// Receiver adjustments for field access / method calls through a sigil:
    /// `&T`/`*T` auto-deref to the pointee; `-T` only allows `.upgrade()`.
    pub(crate) fn ownership_receiver(&self, recv_ty: Type, member: &str, is_method: bool) -> Result<Type, TypeError> {
        match recv_ty {
            Type::Unique(inner) | Type::Shared(inner) => Ok(self.resolve(&inner)),
            Type::Weak(inner) => {
                if self.nogc_strict && !(is_method && member == "upgrade") {
                    return Err(TypeError::Ownership(format!(
                        "-T must be upgraded before use: `{member}` on a weak reference; use w.upgrade()"
                    )));
                }
                Ok(Type::Weak(inner))
            }
            other => Ok(other),
        }
    }

    /// Pre-pass for strict mode: class names (bare `T` = `&T`) and declared
    /// function signatures (argument/return boundary checks).
    pub(crate) fn collect_ownership_decls(&mut self, items: &[Node]) {
        if !self.nogc_strict {
            return;
        }
        for item in items {
            if let Node::Class(class) = item {
                self.class_names.insert(class.name.clone());
            }
        }
        for item in items {
            if let Node::Function(func) = item {
                let params: Vec<Option<Type>> = func
                    .params
                    .iter()
                    .map(|p| p.ty.as_ref().map(|t| self.ast_type_to_type(t)))
                    .collect();
                let ret = func.return_type.as_ref().map(|t| self.ast_type_to_type(t));
                self.fn_sigs.insert(func.name.clone(), (params, ret));
            }
        }
    }

    /// Strict-mode argument check for a call to a known module function.
    pub(crate) fn check_call_ownership(
        &mut self,
        callee: &Expr,
        args: &[simple_parser::ast::Argument],
        arg_types: &[Type],
    ) -> Result<(), TypeError> {
        if !self.nogc_strict {
            return Ok(());
        }
        let Expr::Identifier(name) = callee else {
            return Ok(());
        };
        let Some((params, _)) = self.fn_sigs.get(name).cloned() else {
            return Ok(());
        };
        for (idx, (arg_ty, param)) in arg_types.iter().zip(params.iter()).enumerate() {
            if args.get(idx).is_some_and(|a| a.name.is_some()) {
                continue;
            }
            if let Some(param_ty) = param {
                self.check_ownership_flow(arg_ty, param_ty, &format!("argument {} of {name}()", idx + 1))?;
            }
        }
        Ok(())
    }
}
