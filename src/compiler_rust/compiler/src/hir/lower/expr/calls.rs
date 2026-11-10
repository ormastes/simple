//! Function call expression lowering
//!
//! This module contains expression lowering logic for function calls,
//! including special builtins (async, I/O, math/conversion) and spawn.

use simple_parser::{self as ast, Expr, Span};

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::deprecation_warning::DeprecationWarning;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;
use crate::value::{BUILTIN_JOIN, BUILTIN_REPLY, BUILTIN_SPAWN};

impl Lowerer {
    /// Lower a function call expression to HIR
    ///
    /// Handles:
    /// - Class/struct construction: ClassName(args) - Python-style constructors
    /// - Async/generator builtins (generator, future, await)
    /// - I/O builtins (print, println, eprint, eprintln)
    /// - Math/conversion builtins (abs, min, max, sqrt, etc.)
    /// - Actor spawn
    /// - Regular function calls
    ///
    /// Also enforces purity constraints in contract expressions.
    pub(super) fn lower_call(
        &mut self,
        callee: &Expr,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // PAREN-FORM STRUCT SPREAD: `S(..base, field: v)`.
        // `Expr::StructSpread` is produced ONLY by `parse_arguments`, so an
        // argument list carrying one is a struct-update construction and never
        // an ordinary call. Split it out here rather than threading an
        // `Option<&Expr>` through every builtin branch below.
        if args.iter().any(|a| matches!(a.value, Expr::StructSpread(_))) {
            return self.lower_ctor_with_spread(callee, args, ctx);
        }
        // Check for special builtins: generator, future, spawn, await, print, etc.
        if let Expr::Identifier(name) = callee {
            if let Some((type_name, "new")) = name.rsplit_once('.') {
                if let Some(type_id) = self.module.types.lookup(type_name) {
                    if matches!(self.module.types.get(type_id), Some(HirType::Bitfield { .. })) {
                        return self.lower_bitfield_constructor(type_id, args, ctx);
                    }
                }
            }

            if let Some((type_name, member)) = name.split_once("::").or_else(|| name.split_once('.')) {
                if let Some(type_id) = self.static_enum_variant_type(type_name, member) {
                    return self.lower_static_enum_variant_call(type_name, member, type_id, args, ctx);
                }
            }

            // Short enum-constructor grammar: Some(x), None(), Ok(x), Err(x).
            // Lower these as regular calls to the bare constructor symbol so MIR
            // can canonicalize them into Option*/Result* instructions.
            match (name.as_str(), args.len()) {
                ("Some", 1) | ("Ok", 1) | ("Err", 1) | ("None", 0) => {
                    let func_hir = Box::new(HirExpr {
                        kind: HirExprKind::Global(name.clone()),
                        ty: TypeId::ANY,
                    });
                    let args_hir = self.lower_call_args(args, ctx)?;
                    // Keep an already-known function or nominal record payload
                    // on Some, including record variables and call results.
                    // Otherwise `Some(owned)` binds ANY and a later field read
                    // loses its authored record owner. Other shapes stay erased;
                    // no field-name or layout guessing may create an owner.
                    let ty = match (name.as_str(), args_hir.first()) {
                        ("Some", Some(payload))
                            if matches!(self.module.types.get(payload.ty), Some(HirType::Function { .. } | HirType::Struct { .. })) =>
                        {
                            self.module.types.register(HirType::Enum {
                                name: "Option".to_string(),
                                variants: vec![
                                    ("Some".to_string(), Some(vec![payload.ty])),
                                    ("None".to_string(), None),
                                ],
                                generic_params: vec!["T".to_string()],
                                is_generic_template: false,
                                type_bindings: std::collections::HashMap::from([("T".to_string(), payload.ty)]),
                            })
                        }
                        _ => TypeId::ANY,
                    };
                    return Ok(HirExpr {
                        kind: HirExprKind::Call {
                            func: func_hir,
                            args: args_hir,
                        },
                        ty,
                    });
                }
                _ => {}
            }

            // Check if this is a class/struct constructor call: ClassName(args)
            // Python-style construction: Service() calls the class constructor
            //
            // Primitive type names (str, text, int, bool, ...) are registered
            // in the type registry too, but a call on them is a CAST, not a
            // constructor. Building a StructInit for e.g. `str(5)` produced a
            // bogus one-field struct typed STRING which rt_string_concat
            // rejected (len=-1 → NIL), dropping `"x=" + str(5)` to empty (#66).
            // Skip primitives here so lower_utility_builtin lowers them as Cast.
            let ctor_ty = self.resolve_constructor_type(name);
            if let Some(struct_ty) = ctor_ty {
                if matches!(self.module.types.get(struct_ty), Some(HirType::Bitfield { .. })) {
                    return self.lower_bitfield_constructor(struct_ty, args, ctx);
                }
                // ROOT FIX (bug simpleos_native_build_field_defaults_and_boxed_trait_dispatch,
                // 2026-07-16): this used to be `lower_call_args`, which
                // "lowers arguments as positional field initializers" —
                // dropping `arg.name` entirely and lowering values in
                // literal-source order regardless of the struct's declared
                // field order. See `lower_struct_init_fields` in
                // collections.rs for the full root-cause writeup; it
                // reorders named args to their declared slot and fills any
                // field the call site omits (relying on a class-level
                // default) with `nil` instead of leaving it unset.
                let provided: Vec<(Option<&str>, &Expr)> = args.iter().map(|a| (a.name.as_deref(), &a.value)).collect();
                let (fields_hir, binding) = self.lower_struct_init_fields(name, struct_ty, &provided, None, ctx)?;
                return Ok(Self::finish_struct_init(struct_ty, fields_hir, binding));
            } else if self.lenient_types
                && name.starts_with(|c: char| c.is_ascii_uppercase())
                && args.iter().any(|a| a.name.is_some())
            {
                // In lenient mode, uppercase identifier with named arguments is likely
                // a struct construction even if the type isn't in the registry.
                // Use TypeId::ANY since we don't have the actual type info.
                // Struct type is unresolved (ANY) here, so
                // lower_struct_init_fields falls back to source-order lowering
                // (its "unresolvable struct" branch) — same effective
                // behavior as before, just centralized through one helper.
                let provided: Vec<(Option<&str>, &Expr)> = args.iter().map(|a| (a.name.as_deref(), &a.value)).collect();
                let (fields_hir, binding) = self.lower_struct_init_fields(name, TypeId::ANY, &provided, None, ctx)?;
                return Ok(Self::finish_struct_init(TypeId::ANY, fields_hir, binding));
            }

            // Handle special async/generator builtins
            if let Some(result) = self.lower_async_builtin(name, args, ctx)? {
                return Ok(result);
            }

            // Handle I/O builtins
            if let Some(result) = self.lower_io_builtin(name, args, ctx)? {
                return Ok(result);
            }

            // Handle math/conversion builtins
            if let Some(result) = self.lower_utility_builtin(name, args, ctx)? {
                return Ok(result);
            }

            // Handle the abort builtin
            if let Some(result) = self.lower_abort_builtin(name, args, ctx)? {
                return Ok(result);
            }

            // Check for spawn
            if name == BUILTIN_SPAWN && args.len() == 1 {
                let body_hir = Box::new(self.lower_expr(&args[0].value, ctx)?);
                return Ok(HirExpr {
                    kind: HirExprKind::ActorSpawn { body: body_hir },
                    ty: TypeId::I64,
                });
            }

            // Check for join
            if name == BUILTIN_JOIN && args.len() == 1 {
                let actor_hir = self.lower_expr(&args[0].value, ctx)?;
                return Ok(HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: "join".to_string(),
                        args: vec![actor_hir],
                    },
                    ty: TypeId::I64,
                });
            }

            // Check for reply
            if name == BUILTIN_REPLY && args.len() == 1 {
                let message_hir = self.lower_expr(&args[0].value, ctx)?;
                return Ok(HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: "reply".to_string(),
                        args: vec![message_hir],
                    },
                    ty: TypeId::NIL,
                });
            }

            // GPU intrinsics: gpu_global_id_x, gpu_local_id_x, gpu_syncthreads, etc.
            if let Some(gpu_result) = self.lower_gpu_function_intrinsic(name, args, ctx)? {
                return Ok(gpu_result);
            }

            // CTR-030-032: Check for impure function calls in contract expressions
            if ctx.contract_ctx.is_some() {
                self.check_contract_purity(name)?;
            }

            // Check for deprecated function usage
            if self.is_deprecated(name) {
                let message = self.deprecation_message(name).map(|s| s.to_string());
                let suggestion = self.find_non_deprecated_function_alternative(name);
                let span = if let Expr::Identifier(_) = callee {
                    // Use a dummy span for now - in a real implementation we'd get the actual span
                    Span::new(0, 0, 1, 1)
                } else {
                    Span::new(0, 0, 1, 1)
                };
                self.deprecation_warnings
                    .add(DeprecationWarning::function(span, name.clone(), message, suggestion));
            }
        }

        // Handle static method calls: ClassName.method(args)
        // This handles Expr::Path with 2 segments like Container.with_profile()
        if let Expr::Path(segments) = callee {
            if segments.len() == 2 {
                if let Some(type_id) = self.module.types.lookup(&segments[0]) {
                    if matches!(self.module.types.get(type_id), Some(HirType::Bitfield { .. })) && segments[1] == "new"
                    {
                        return self.lower_bitfield_constructor(type_id, args, ctx);
                    }
                }
                return self.lower_static_member_call_with_sugar(&segments[0], &segments[1], args, ctx);
            }
        }

        // Regular function call
        let func_hir = Box::new(self.lower_expr(callee, ctx)?);
        // Preserve the resolved symbol even before its body has been lowered:
        // forward and recursive callees can still carry a scalar return type.
        let ret_ty = match (&func_hir.kind, callee) {
            (HirExprKind::Global(symbol), Expr::Identifier(_)) => {
                self.call_return_type(&Expr::Identifier(symbol.clone()), func_hir.ty)
            }
            _ => self.call_return_type(callee, func_hir.ty),
        };
        let ret_ty = self.refine_generic_identity_return(callee, args, ret_ty, ctx);
        // Check the RESOLVED symbol, not the bare callee name: in a flattened
        // unit with a cross-module same-named collision, `func_hir.kind` may
        // carry a different (owner-mangled) symbol than `callee`'s bare text,
        // and `proven_nonescaping_functions`/other per-symbol sets below are
        // keyed by the symbol `lower_function` actually emitted
        // (`flatten_emitted_symbol`), not by the ambiguous bare name.
        let resolved_callee_symbol = match (&func_hir.kind, callee) {
            (HirExprKind::Global(symbol), Expr::Identifier(_)) => Some(symbol.as_str()),
            (_, Expr::Identifier(name)) => Some(name.as_str()),
            _ => None,
        };
        let proven_nonescaping = resolved_callee_symbol
            .is_some_and(|symbol| self.proven_nonescaping_functions.contains(symbol))
            && !self.is_reference_type(ret_ty);
        // A lambda passed positionally to a fn-typed parameter takes that
        // parameter's declared callback param types. Without this, a
        // placeholder lambda (`apply(_1 + 1, 4)`) defaulted its params to ANY
        // while the callee invokes it with raw scalars, so the JIT computed on
        // a tagged/raw mix (`apply(_1 + 1, 4)` returned 40, not 5).
        let callee_fn_param_types: Vec<Option<Vec<TypeId>>> = match self.module.types.get(func_hir.ty) {
            Some(HirType::Function { params, .. }) if args.iter().all(|a| a.name.is_none()) => params
                .clone()
                .into_iter()
                .map(|p| match self.module.types.get(p) {
                    Some(HirType::Function { params, .. }) => Some(params.clone()),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        };
        let has_typed_lambda_arg = args.iter().enumerate().any(|(i, a)| {
            matches!(a.value, Expr::Lambda { .. }) && matches!(callee_fn_param_types.get(i), Some(Some(_)))
        });
        let mut args_hir = if has_typed_lambda_arg {
            let capability_checkpoint = proven_nonescaping.then(|| self.capability_env.clone());
            let mut out = Vec::with_capacity(args.len());
            for (i, arg) in args.iter().enumerate() {
                match (&arg.value, callee_fn_param_types.get(i)) {
                    (Expr::Lambda { params, body, capture_all, .. }, Some(Some(param_tys))) => {
                        let param_tys = param_tys.clone();
                        out.push(self.lower_lambda_with_param_types(params, body, *capture_all, ctx, &param_tys)?);
                    }
                    _ => out.push(self.lower_expr(&arg.value, ctx)?),
                }
            }
            if let Some(checkpoint) = capability_checkpoint {
                self.capability_env = checkpoint;
            }
            out
        } else if proven_nonescaping {
            self.lower_nonescaping_call_args(args, ctx)?
        } else if matches!(callee, Expr::Identifier(name) if name == "array_sort_by")
            && matches!(args, [_, ast::Argument { value: Expr::Lambda { .. }, .. }])
        {
            let first = self.lower_expr(&args[0].value, ctx)?;
            let callback = if let (
                Some(HirType::Array { element, .. }),
                Expr::Lambda { params, body, capture_all, .. },
            ) = (self.module.types.get(first.ty), &args[1].value)
            {
                let element = *element;
                self.lower_lambda_with_param_types(params, body, *capture_all, ctx, &[element, element])?
            } else {
                self.lower_expr(&args[1].value, ctx)?
            };
            vec![first, callback]
        } else {
            self.lower_call_args(args, ctx)?
        };

        // BOOL-ARG STATIC ADMISSION (doc/08_tracking/bug/bool_typed_parameter_accepts_non_bool_and_jit_corrupts_it_2026-08-04):
        // lowering-side mirror of the interpreter pre-scan in `bind_args`: a
        // literal non-bool argument at a `bool`-declared parameter of a
        // directly-named function is a lowering error, so the JIT lane cannot
        // re-tag it into a corrupt value. Existence probes (`x.?`), Option
        // payloads, and non-literal expressions keep the runtime PRESENCE
        // contract. Spreads are statically uncounted and keep the runtime
        // contract for every spread-touched slot.
        if let (Expr::Identifier(_), HirExprKind::Global(symbol)) = (callee, &func_hir.kind) {
            if let Some(slots) = self.fn_param_bool.get(symbol) {
                if !slots.is_empty() && !args.iter().any(|a| matches!(a.value, Expr::Spread(_))) {
                    let named: std::collections::HashSet<&str> =
                        args.iter().filter_map(|a| a.name.as_deref()).collect();
                    let names = self.fn_param_names.get(symbol);
                    let mut cursor = 0usize;
                    for arg in args {
                        let slot = match arg.name.as_deref() {
                            Some(n) => names.and_then(|ns| ns.iter().position(|p| p == n)),
                            None => {
                                // Advance past slots a named argument claimed.
                                while cursor < slots.len() {
                                    let claimed = names
                                        .and_then(|ns| ns.get(cursor))
                                        .map(|p| named.contains(p.as_str()))
                                        .unwrap_or(false);
                                    if !claimed {
                                        break;
                                    }
                                    cursor += 1;
                                }
                                let s = (cursor < slots.len()).then_some(cursor);
                                cursor += 1;
                                s
                            }
                        };
                        if let Some(i) = slot {
                            if slots[i] {
                                if let Some(kind) =
                                    crate::interpreter::interpreter_call::non_bool_literal_arg_kind(&arg.value)
                                {
                                    let pname = names
                                        .and_then(|ns| ns.get(i))
                                        .map(String::as_str)
                                        .unwrap_or("?");
                                    return Err(LowerError::Unsupported(format!(
                                        "type mismatch: parameter '{pname}' is declared 'bool' but the argument is a {kind} literal"
                                    )));
                                }
                            }
                        }
                    }
                }
            }
        }

        // M12 3b: fill omitted trailing arguments from the callee's parameter
        // defaults, for a directly-named free function called purely
        // positionally (same-module table first, then the importing file's
        // cross-module contract table). A default that cannot be materialised
        // at the call site is a compile error (`fill_omitted_default_args`):
        // codegen would otherwise pad the slot with tagged nil.
        if let (Expr::Identifier(name), HirExprKind::Global(symbol)) = (callee, &func_hir.kind) {
            let own = self.own_declared_function_names.contains(name);
            let params = self.fn_param_defaults.get(symbol).or_else(|| {
                if own { return None; }
                self.current_file.as_ref().and_then(|path| {
                    self.imported_fn_param_defaults
                        .get(&crate::interpreter::normalize_path_key(path))
                        .and_then(|contracts| contracts.get(name))
                })
            }).cloned();
            if args.iter().all(|a| a.name.is_none()) {
                if let Some(params) = params {
                    self.fill_omitted_default_args(symbol, &params, &mut args_hir, ctx)?;
                }
            } else if let Some(params) = params {
                // Named arguments: map every argument onto its declared slot
                // and fill the rest from constant defaults. Without this the
                // args were passed in source order with omitted slots left
                // unset (tagged nil) - bug
                // jit_layout_run_full_with_ports_nil_receiver (rc=139).
                let names = self.fn_param_names.get(symbol).or_else(|| {
                    if own { return None; }
                    self.current_file.as_ref().and_then(|path| {
                        self.imported_fn_param_names
                            .get(&crate::interpreter::normalize_path_key(path))
                            .and_then(|contracts| contracts.get(name))
                    })
                }).cloned();
                let Some(names) = names else {
                    return Err(LowerError::Unsupported(format!(
                        "call to `{symbol}` uses named arguments but its parameter names are unknown here; \
                         pass the arguments positionally"
                    )));
                };
                // Empty names = variadic callee: keep the legacy path.
                if !names.is_empty() {
                    args_hir = self.bind_named_call_args(symbol, &names, &params, args, args_hir, ctx)?;
                }
            }
        }

        // Prefer the declared return type for the named callee when we know it.
        // This keeps local variables initialized from imported/helper calls on a
        // concrete type path instead of degrading to ANY at the next field access.
        Ok(HirExpr {
            kind: HirExprKind::Call {
                func: func_hir,
                args: args_hir,
            },
            ty: ret_ty,
        })
    }

    /// Map a call that uses named arguments onto the callee's declared slots.
    /// Positional arguments fill slots 0..n, each named argument fills the
    /// slot of the same name, and every remaining slot takes its constant
    /// default (lowered in the caller, once). A required slot left unfilled,
    /// an unknown or duplicated name, or a non-constant default is a hard
    /// lowering error - never an unset slot that codegen pads with nil.
    /// Arguments are passed in declared slot order.
    pub(super) fn bind_named_call_args(
        &mut self,
        callee: &str,
        names: &[String],
        defaults: &[Option<Expr>],
        args: &[ast::Argument],
        args_hir: Vec<HirExpr>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<Vec<HirExpr>> {
        let mut slots: Vec<Option<HirExpr>> = (0..names.len()).map(|_| None).collect();
        let mut next_positional = 0usize;
        for (arg, hir) in args.iter().zip(args_hir) {
            let index = match arg.name.as_deref() {
                None => {
                    // Positional arguments fill the lowest UNFILLED slots in
                    // order: a named argument may precede them (the
                    // interpreter binds `f(1, c: 3, 2, 4)` as a=1, b=2, c=3,
                    // d=4), so the cursor must skip slots a named argument
                    // already took. Advancing blindly from the argument
                    // position collided with earlier named slots ("parameter
                    // N more than once or beyond its arity",
                    // seed_jit_hir_positional_after_named_arg_2026-11-04).
                    while next_positional < slots.len() && slots[next_positional].is_some() {
                        next_positional += 1;
                    }
                    let i = next_positional;
                    next_positional += 1;
                    i
                }
                Some(n) => names.iter().position(|p| p == n).ok_or_else(|| {
                    LowerError::Unsupported(format!("call to `{callee}` names unknown parameter `{n}`"))
                })?,
            };
            match slots.get_mut(index) {
                Some(slot @ None) => *slot = Some(hir),
                _ => {
                    return Err(LowerError::Unsupported(format!(
                        "call to `{callee}` passes parameter {} more than once or beyond its arity",
                        index + 1
                    )));
                }
            }
        }
        let mut out = Vec::with_capacity(slots.len());
        for (index, slot) in slots.into_iter().enumerate() {
            match slot {
                Some(hir) => out.push(hir),
                None => match defaults.get(index).and_then(|d| d.as_ref()) {
                    Some(expr) if self.is_fillable_default(callee, expr) => out.push(self.lower_expr(expr, ctx)?),
                    Some(_) => {
                        return Err(LowerError::Unsupported(format!(
                            "call to `{callee}` omits argument {} whose default is not a call-site constant; \
                             a cross-module/native call cannot evaluate it, pass the argument explicitly",
                            index + 1
                        )));
                    }
                    None => {
                        return Err(LowerError::Unsupported(format!(
                            "call to `{callee}` omits required argument {} (`{}`)",
                            index + 1, names[index]
                        )));
                    }
                },
            }
        }
        Ok(out)
    }

    /// Append the callee's default for every omitted trailing positional
    /// argument. Defaults are lowered in the CALLER, left to right, once per
    /// call, after all explicit arguments - so only self-contained constant
    /// expressions (`is_constant_default`) are admitted: they cannot name
    /// caller-scope locals, sibling parameters, or callee-module globals the
    /// caller may not import. Any other omitted default is a compile error
    /// rather than an unfilled slot, because native codegen pads a missing
    /// argument with tagged nil and the callee then reads garbage (bug class:
    /// stage3 `lower_module` SIGSEGV on an omitted `[MirFunction] = []`).
    /// A slot without a default (a required parameter) stops the fill and is
    /// left to arity checking.
    pub(super) fn fill_omitted_default_args(
        &mut self,
        callee: &str,
        defaults: &[Option<Expr>],
        args_hir: &mut Vec<HirExpr>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<()> {
        let first_omitted = args_hir.len();
        for (index, slot) in defaults.iter().enumerate().skip(first_omitted) {
            match slot {
                Some(expr) if self.is_fillable_default(callee, expr) => {
                    let lowered = self.lower_expr(expr, ctx)?;
                    args_hir.push(lowered);
                }
                Some(_) => {
                    return Err(LowerError::Unsupported(format!(
                        "call to `{callee}` omits argument {} whose default is not a call-site constant; \
                         a cross-module/native call cannot evaluate it, pass the argument explicitly",
                        index + 1
                    )));
                }
                None => break,
            }
        }
        Ok(())
    }

    /// The constructor type the caller sees must be the very type the callee
    /// module declares: the callee has exactly one defining file, and the
    /// caller imported `type_name` from that single file and no other (an
    /// unrelated same-named type, directly or via glob, adds a second owner).
    fn ctor_type_matches_callee(&self, callee: &str, type_name: &str) -> bool {
        match (self.imported_fn_owners.get(callee), self.imported_type_owners.get(type_name)) {
            (Some(f), Some(t)) => f.len() == 1 && f == t,
            _ => false,
        }
    }

    /// `is_constant_default`, plus a constructor call `T(const, ...)` whose `T`
    /// resolves in the CALLER to a struct/class not declared by the caller's
    /// own module (a local `T` would shadow the callee's type). Constructor
    /// arguments must themselves be fillable, so nothing captures caller scope.
    /// (lean_native_constructor_default_argument_2026_10_21)
    pub(super) fn is_fillable_default(&self, fn_name: &str, expr: &Expr) -> bool {
        if Self::is_constant_default(expr) {
            return true;
        }
        match expr {
            Expr::Call { callee, args } => match callee.as_ref() {
                Expr::Identifier(name) => {
                    !self.own_declared_type_names.contains(name)
                        && (self.own_imported_names.contains(name) || self.own_imported_names.contains("*"))
                        && self.resolve_constructor_type(name).is_some()
                        && self.ctor_type_matches_callee(fn_name, name)
                        && args.iter().all(|a| self.is_fillable_default(fn_name, &a.value))
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// True for default-value expressions that are self-contained constants —
    /// safe to lower at a call site because they cannot reference caller-scope
    /// locals or sibling parameters. Conservative: anything not provably
    /// constant (identifiers, calls, field access, …) returns false and is left
    /// unfilled rather than risk a silent miscompile.
    pub(super) fn is_constant_default(expr: &Expr) -> bool {
        match expr {
            Expr::Integer(_)
            | Expr::Float(_)
            | Expr::String(_)
            | Expr::Bool(_)
            | Expr::Nil
            | Expr::Symbol(_)
            | Expr::Atom(_) => true,
            // Ordinary quoted strings use FString syntax too. Only literal
            // parts are safe here; interpolation must not capture caller scope.
            Expr::FString { parts, .. } => parts.iter().all(|part| matches!(part, ast::FStringPart::Literal(_))),
            Expr::TypedInteger(..) | Expr::TypedFloat(..) | Expr::TypedString(..) => true,
            Expr::Unary { operand, .. } => Self::is_constant_default(operand),
            Expr::Binary { left, right, .. } => Self::is_constant_default(left) && Self::is_constant_default(right),
            // Container literals allocate a FRESH value per call, which is the
            // per-call default semantics; admitted when every element is itself
            // a constant (an empty literal vacuously).
            Expr::Array(items) | Expr::VecLiteral(items) | Expr::Tuple(items) => {
                items.iter().all(Self::is_constant_default)
            }
            Expr::Dict(entries) => entries
                .iter()
                .all(|(key, value)| Self::is_constant_default(key) && Self::is_constant_default(value)),
            _ => false,
        }
    }

    /// Resolve `name` to the struct/class TypeId a paren-call constructor
    /// would build, or `None` when `name` is not a constructor.
    ///
    /// Primitive type names (`str`, `text`, `int`, `bool`, ...) are registered
    /// in the type registry too, but a call on them is a CAST, not a
    /// constructor. Building a StructInit for e.g. `str(5)` produced a bogus
    /// one-field struct typed STRING which rt_string_concat rejected
    /// (len=-1 -> NIL), dropping `"x=" + str(5)` to empty (#66). They are
    /// excluded here so `lower_utility_builtin` lowers them as Cast.
    pub(super) fn resolve_constructor_type(&self, name: &str) -> Option<TypeId> {
        let bare_ctor_ty = self.module.types.lookup(name);
        let bare_is_primitive = bare_ctor_ty.is_some_and(|ty_id| {
            matches!(
                self.module.types.get(ty_id),
                Some(
                    HirType::Void
                        | HirType::Bool
                        | HirType::Any
                        | HirType::Char
                        | HirType::Int { .. }
                        | HirType::Float { .. }
                        | HirType::String
                        | HirType::Nil
                )
            )
        });
        if bare_is_primitive {
            return None;
        }
        self.global_struct_key_for_name(name)
            .and_then(|key| self.module.types.lookup(&key))
            .or(bare_ctor_ty)
    }

    /// Lower a PAREN-form struct-update construction `S(..base, field: v)`.
    ///
    /// Reached only when `lower_call` saw an `Expr::StructSpread` argument.
    /// Every failure path here is a HARD ERROR: `..base` in a position that is
    /// not a struct construction used to parse as `Expr::Range { start: None,
    /// end: base }`, lower to `rt_range(0, <tagged object pointer>)` and HANG
    /// the compiler materialising billions of elements
    /// (`doc/08_tracking/bug/struct_spread_paren_form_parses_as_range_2026-08-30.md`).
    /// A loud diagnostic is the whole point; nothing here may fall through to
    /// a generic call.
    fn lower_ctor_with_spread(
        &mut self,
        callee: &Expr,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let spreads: Vec<&Expr> = args
            .iter()
            .filter_map(|a| match &a.value {
                Expr::StructSpread(base) => Some(base.as_ref()),
                _ => None,
            })
            .collect();
        if spreads.len() > 1 {
            return Err(LowerError::Unsupported(format!(
                "{} struct spreads (`..base`) in one construction: at most one is allowed",
                spreads.len()
            )));
        }
        let base = spreads[0];

        let Expr::Identifier(name) = callee else {
            return Err(LowerError::Unsupported(
                "struct spread `..base` is only valid in a struct/class construction such as \
                 `S(..base, field: value)`"
                    .to_string(),
            ));
        };

        let Some(struct_ty) = self.resolve_constructor_type(name) else {
            return Err(LowerError::Unsupported(format!(
                "struct spread `..base` in a call to `{name}`, which does not name a struct or \
                 class constructor"
            )));
        };
        if matches!(self.module.types.get(struct_ty), Some(HirType::Bitfield { .. })) {
            return Err(LowerError::Unsupported(format!(
                "struct spread `..base` is not supported for bitfield `{name}`"
            )));
        }

        let provided: Vec<(Option<&str>, &Expr)> = args
            .iter()
            .filter(|a| !matches!(a.value, Expr::StructSpread(_)))
            .map(|a| (a.name.as_deref(), &a.value))
            .collect();
        let (fields_hir, binding) = self.lower_struct_init_fields(name, struct_ty, &provided, Some(base), ctx)?;
        Ok(Self::finish_struct_init(struct_ty, fields_hir, binding))
    }

    pub(super) fn lower_bitfield_constructor(
        &mut self,
        bitfield_ty: TypeId,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        if args.len() != 1 || args[0].name.is_some() {
            return Err(LowerError::Unsupported(
                "bitfield constructors currently accept exactly one positional raw value".to_string(),
            ));
        }

        let value_hir = self.lower_expr(&args[0].value, ctx)?;
        Ok(HirExpr {
            kind: HirExprKind::Cast {
                expr: Box::new(value_hir),
                target: bitfield_ty,
            },
            ty: bitfield_ty,
        })
    }

    /// Handle async/generator builtins: generator, future, await
    ///
    /// Returns Some(HirExpr) if the name matches a builtin, None otherwise.
    fn lower_async_builtin(
        &mut self,
        name: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        match name {
            "generator" => {
                if args.len() == 1 {
                    let body_hir = Box::new(self.lower_expr(&args[0].value, ctx)?);
                    return Ok(Some(HirExpr {
                        kind: HirExprKind::GeneratorCreate { body: body_hir },
                        ty: TypeId::I64,
                    }));
                }
                // 2+ args → not a builtin, fall through to regular call
                Ok(None)
            }
            "future" => {
                if args.len() != 1 {
                    return Err(LowerError::Unsupported(
                        "future expects exactly one argument".to_string(),
                    ));
                }
                let body_hir = Box::new(self.lower_expr(&args[0].value, ctx)?);
                Ok(Some(HirExpr {
                    kind: HirExprKind::FutureCreate { body: body_hir },
                    ty: TypeId::I64,
                }))
            }
            "await" => {
                if args.len() != 1 {
                    return Err(LowerError::Unsupported(
                        "await expects exactly one argument".to_string(),
                    ));
                }
                let future_hir = Box::new(self.lower_expr(&args[0].value, ctx)?);
                Ok(Some(HirExpr {
                    kind: HirExprKind::Await(future_hir),
                    ty: TypeId::I64,
                }))
            }
            _ => Ok(None),
        }
    }

    /// Handle I/O builtins: print, print_raw, eprint, eprint_raw, dprint
    ///
    /// Note: println and eprintln are deprecated (show runtime errors)
    /// Returns Some(HirExpr) if the name matches a builtin, None otherwise.
    fn lower_io_builtin(
        &mut self,
        name: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        if matches!(
            name,
            "print" | "print_raw" | "eprint" | "eprint_raw" | "dprint" | "println" | "eprintln"
        ) {
            Ok(Some(self.lower_builtin_call(name, args, TypeId::NIL, ctx)?))
        } else {
            Ok(None)
        }
    }

    /// Handle the `panic(msg)` abort builtin.
    ///
    /// `panic` is a registered runtime builtin everywhere else in the compiler —
    /// the interpreter extern table (`insert_simple!("panic", ...)`), the native
    /// binary stub list, and the C runtime (`void panic(int64_t msg)`) — but HIR
    /// lowering never knew it. That made `panic(...)` lower as a plain
    /// identifier, fail with `UnknownVariable: panic`, and (because a HIR
    /// lowering error discards the WHOLE module) drop every module that
    /// transitively uses it back to the interpreter. `FailSafeResult.unwrap` is
    /// the load-bearing case: it is on the web render path.
    ///
    /// Type is ANY, not NIL: `panic` diverges, so it must unify with whatever
    /// the surrounding expression needs (e.g. the `case Err(e): panic(...)` arm
    /// of a `-> T` match). Stamping NIL would inject a bogus concrete type.
    /// Returns Some(HirExpr) if the name matches, None otherwise.
    fn lower_abort_builtin(
        &mut self,
        name: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        if name != "panic" {
            return Ok(None);
        }
        match args.len() {
            // Bare `panic()` — the interpreter defaults the message to "panic";
            // the native symbol takes one argument, so synthesize it here.
            0 => Ok(Some(HirExpr {
                kind: HirExprKind::BuiltinCall {
                    name: "panic".to_string(),
                    args: vec![HirExpr {
                        kind: HirExprKind::String("panic".to_string()),
                        ty: TypeId::STRING,
                    }],
                },
                ty: TypeId::ANY,
            })),
            1 => Ok(Some(self.lower_builtin_call(name, args, TypeId::ANY, ctx)?)),
            n => Err(LowerError::Unsupported(format!(
                "panic expects at most one argument, got {n}"
            ))),
        }
    }

    /// Handle math/conversion builtins
    ///
    /// Includes: abs, min, max, sqrt, floor, ceil, pow, to_string, to_int,
    /// and cast-style calls: int(x), text(x), bool(x), char(x), i8(x)..u64(x), f32(x), f64(x).
    /// Returns Some(HirExpr) if the name matches a builtin, None otherwise.
    fn lower_utility_builtin(
        &mut self,
        name: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        if args.len() == 1 {
            let cast_target = match name {
                "i8" => Some(TypeId::I8),
                "i16" => Some(TypeId::I16),
                "i32" => Some(TypeId::I32),
                "i64" | "int" => Some(TypeId::I64),
                "u8" => Some(TypeId::U8),
                "u16" => Some(TypeId::U16),
                "u32" => Some(TypeId::U32),
                "u64" => Some(TypeId::U64),
                "f32" => Some(TypeId::F32),
                "f64" | "float" => Some(TypeId::F64),
                "bool" => Some(TypeId::BOOL),
                "text" | "str" | "String" => Some(TypeId::STRING),
                "char" => Some(TypeId::CHAR),
                _ => None,
            };
            if let Some(target) = cast_target {
                let inner = self.lower_expr(&args[0].value, ctx)?;
                // The CALL form `f64(text)` / `i32(text)` PARSES its text, like
                // `text.to_f64()` / `text.to_int()` and the interpreter's `T(x)`
                // builtins (unparsable -> 0.0 / 0). It must not share the
                // `x as T` Cast, whose text->number rule is the single-character
                // code point (`"x" as f64 == 120.0`, `"5" as i32 == 53`).
                // doc/08_tracking/bug/float_parse_call_failure_value_differs_from_seed_2026-10-10.md
                if inner.ty == TypeId::STRING {
                    let is_float = matches!(target, TypeId::F32 | TypeId::F64);
                    let is_int = matches!(
                        target,
                        TypeId::I8
                            | TypeId::I16
                            | TypeId::I32
                            | TypeId::I64
                            | TypeId::U8
                            | TypeId::U16
                            | TypeId::U32
                            | TypeId::U64
                    );
                    if is_float || is_int {
                        let (method, parsed_ty) = if is_float {
                            ("to_f64", TypeId::F64)
                        } else {
                            ("to_int", TypeId::I64)
                        };
                        let parsed = HirExpr {
                            kind: HirExprKind::MethodCall {
                                receiver: Box::new(inner),
                                method: method.to_string(),
                                args: Vec::new(),
                                dispatch: DispatchMode::Static,
                            },
                            ty: parsed_ty,
                        };
                        if target == parsed_ty {
                            return Ok(Some(parsed));
                        }
                        return Ok(Some(HirExpr {
                            kind: HirExprKind::Cast {
                                expr: Box::new(parsed),
                                target,
                            },
                            ty: target,
                        }));
                    }
                }
                return Ok(Some(HirExpr {
                    kind: HirExprKind::Cast {
                        expr: Box::new(inner),
                        target,
                    },
                    ty: target,
                }));
            }
        }

        match name {
            "range" => {
                if !(1..=3).contains(&args.len()) {
                    return Err(LowerError::Unsupported(
                        "range expects one to three arguments".to_string(),
                    ));
                }
                let mut args_hir = self.lower_call_args(args, ctx)?;
                if args_hir.len() == 1 {
                    args_hir.insert(
                        0,
                        HirExpr {
                            kind: HirExprKind::Integer(0),
                            ty: TypeId::I64,
                        },
                    );
                }
                Ok(Some(HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: if args_hir.len() == 3 {
                            "rt_array_range".to_string()
                        } else {
                            "rt_range".to_string()
                        },
                        args: args_hir,
                    },
                    ty: TypeId::ANY,
                }))
            }
            // Result type is DERIVED FROM THE ARGUMENTS, not hard-coded.
            //
            // These seven were pinned to `TypeId::I64` unconditionally. The MIR
            // lowering and both backends are already float-correct for
            // `min`/`max`/`abs` (they lower to a compare + a typed select, and
            // codegen picks fcmp vs icmp off `vreg_types`) — the ONLY thing
            // wrong for float arguments was this label. The observable symptom
            // was `print min(1.5, 2.5)` printing `4609434218613702656`, the
            // verbatim IEEE-754 bit pattern of the correct answer 1.5, because
            // the i64 stamp made `print` render the bits as an integer. Bind
            // the same call to a `val x: f64` and it always printed `1.5`, which
            // is what isolated this to the type and not the computation.
            //
            // Integer callers are unaffected: with i64 arguments this still
            // yields TypeId::I64, exactly as before.
            //
            // `sqrt`/`floor`/`ceil`/`pow` had a SECOND, independent defect that
            // this type derivation did not fix (they fell through to a generic
            // external `Call` to libm using the integer ABI, so they read a
            // return register libm never wrote). That is fixed separately in
            // `lower_libm_math` in mir/lower/lowering_expr_builtin.rs, which
            // routes them to the `rt_math_*` symbols' real f64 ABI — and which
            // depends on the result type derived HERE to decide whether to cast
            // the f64 result back to i64 for integer callers.
            // doc/08_tracking/bug/numeric_builtins_hardcode_i64_result_type_2026-08-10.md
            "abs" | "min" | "max" | "sqrt" | "floor" | "ceil" | "pow" => {
                let args_hir = self.lower_call_args(args, ctx)?;
                let ret_ty = Self::numeric_builtin_result_ty(&args_hir);
                Ok(Some(HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: name.to_string(),
                        args: args_hir,
                    },
                    ty: ret_ty,
                }))
            }
            "to_string" => Ok(Some(self.lower_builtin_call(name, args, TypeId::STRING, ctx)?)),
            "to_int" => Ok(Some(self.lower_builtin_call(name, args, TypeId::I64, ctx)?)),
            "panic" => Ok(Some(self.lower_builtin_call("rt_panic", args, TypeId::NIL, ctx)?)),
            // `exit` must lower as a builtin for the same reason `panic` does,
            // and for one more: it is process control. Names this dispatch does
            // NOT recognize fall through to ordinary function resolution, so a
            // top-level `fn exit` anywhere in the transitive import closure won
            // dispatch in the JIT/native lanes -- and because such a shim need
            // not terminate, failure paths kept running and the process exited
            // 0. (The interpreter lane had the same hole via a different
            // mechanism, the Priority-1 `has_local_def` hatch in
            // interpreter_call/mod.rs; both are fenced now, and this name is
            // listed in `PRELUDE_UNSHADOWABLE`.)
            // doc/08_tracking/bug/prelude_builtins_rebindable_by_transitive_import_2026-08-10.md
            "exit" => Ok(Some(self.lower_builtin_call("rt_exit", args, TypeId::NIL, ctx)?)),
            // Option/Result constructors (needed for stdlib)
            "Some" | "Ok" => {
                // Wrap value in Some/Ok variant - return ANY since it's a generic wrapper
                Ok(Some(self.lower_builtin_call(name, args, TypeId::ANY, ctx)?))
            }
            "None" | "Err" => {
                // None/Err variants - no argument needed for None
                Ok(Some(self.lower_builtin_call(name, args, TypeId::ANY, ctx)?))
            }
            _ => Ok(None),
        }
    }

    /// Result type for the numeric builtins `abs`/`min`/`max`/`sqrt`/`floor`/
    /// `ceil`/`pow`, derived from the lowered argument types.
    ///
    /// Rule: the result is floating point if ANY argument is floating point,
    /// widening to the widest float present (`f64` beats `f32`); otherwise it
    /// keeps the previous `i64` behaviour. A mixed `pow(2.0, 3)` therefore
    /// yields `f64`, matching how the arithmetic actually evaluates, and an
    /// all-integer call is bit-for-bit unchanged from before this fix.
    ///
    /// `TypeId::ANY` arguments (erased/unknown) deliberately do NOT force a
    /// float: nothing is known about them, and defaulting them to float would
    /// regress every integer caller whose argument type inference is
    /// incomplete. They fall through to the `i64` default, which is the
    /// pre-existing behaviour for those callers.
    fn numeric_builtin_result_ty(args: &[HirExpr]) -> TypeId {
        if args.iter().any(|a| a.ty == TypeId::F64) {
            TypeId::F64
        } else if args.iter().any(|a| a.ty == TypeId::F32) {
            TypeId::F32
        } else {
            TypeId::I64
        }
    }

    /// Check if a function can be called in contract expressions
    ///
    /// Contract expressions (in:, out:, invariant:) must only call pure functions.
    /// Some functions are implicitly pure (math builtins, accessors, converters).
    /// Other functions must be explicitly marked as pure.
    fn check_contract_purity(&self, name: &str) -> LowerResult<()> {
        let is_implicitly_pure = matches!(
            name,
            "abs"
                | "min"
                | "max"
                | "sqrt"
                | "floor"
                | "ceil"
                | "pow"
                | "len"
                | "is_empty"
                | "contains"
                | "to_string"
                | "to_int"
                | "old"     // Contract expression: captures value at function entry
                | "result" // Contract expression: accesses return value in postcondition
        );
        if !is_implicitly_pure && !self.is_pure_function(name) {
            return Err(LowerError::ImpureFunctionInContract {
                func_name: name.to_string(),
            });
        }
        Ok(())
    }

    /// Recognize gpu_*_x/y/z function calls as GPU intrinsics.
    fn lower_gpu_function_intrinsic(
        &mut self,
        name: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        let (kind, dim) = match name {
            "gpu_global_id_x" => (GpuIntrinsicKind::GlobalId, 0u8),
            "gpu_global_id_y" => (GpuIntrinsicKind::GlobalId, 1),
            "gpu_global_id_z" => (GpuIntrinsicKind::GlobalId, 2),
            "gpu_thread_id_x" => (GpuIntrinsicKind::LocalId, 0),
            "gpu_thread_id_y" => (GpuIntrinsicKind::LocalId, 1),
            "gpu_thread_id_z" => (GpuIntrinsicKind::LocalId, 2),
            "gpu_local_id_x" => (GpuIntrinsicKind::LocalId, 0),
            "gpu_local_id_y" => (GpuIntrinsicKind::LocalId, 1),
            "gpu_local_id_z" => (GpuIntrinsicKind::LocalId, 2),
            "gpu_block_id_x" => (GpuIntrinsicKind::GroupId, 0),
            "gpu_block_id_y" => (GpuIntrinsicKind::GroupId, 1),
            "gpu_block_id_z" => (GpuIntrinsicKind::GroupId, 2),
            "gpu_block_dim_x" => (GpuIntrinsicKind::LocalSize, 0),
            "gpu_block_dim_y" => (GpuIntrinsicKind::LocalSize, 1),
            "gpu_block_dim_z" => (GpuIntrinsicKind::LocalSize, 2),
            "gpu_grid_dim_x" => (GpuIntrinsicKind::NumGroups, 0),
            "gpu_grid_dim_y" => (GpuIntrinsicKind::NumGroups, 1),
            "gpu_grid_dim_z" => (GpuIntrinsicKind::NumGroups, 2),
            "gpu_syncthreads" => {
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::Barrier,
                        args: vec![],
                    },
                    ty: TypeId::NIL,
                }));
            }
            // GPU memory load/store intrinsics with arguments
            "gpu_load_f64" => {
                let ptr_arg = self.lower_expr(&args[0].value, ctx)?;
                let index_arg = self.lower_expr(&args[1].value, ctx)?;
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::GpuLoadF64,
                        args: vec![ptr_arg, index_arg],
                    },
                    ty: TypeId::F64,
                }));
            }
            "gpu_store_f64" => {
                let ptr_arg = self.lower_expr(&args[0].value, ctx)?;
                let index_arg = self.lower_expr(&args[1].value, ctx)?;
                let value_arg = self.lower_expr(&args[2].value, ctx)?;
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::GpuStoreF64,
                        args: vec![ptr_arg, index_arg, value_arg],
                    },
                    ty: TypeId::NIL,
                }));
            }
            "gpu_load_i64" => {
                let ptr_arg = self.lower_expr(&args[0].value, ctx)?;
                let index_arg = self.lower_expr(&args[1].value, ctx)?;
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::GpuLoadI64,
                        args: vec![ptr_arg, index_arg],
                    },
                    ty: TypeId::I64,
                }));
            }
            "gpu_store_i64" => {
                let ptr_arg = self.lower_expr(&args[0].value, ctx)?;
                let index_arg = self.lower_expr(&args[1].value, ctx)?;
                let value_arg = self.lower_expr(&args[2].value, ctx)?;
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::GpuStoreI64,
                        args: vec![ptr_arg, index_arg, value_arg],
                    },
                    ty: TypeId::NIL,
                }));
            }
            _ => return Ok(None),
        };

        // Create a constant dimension argument
        let dim_arg = HirExpr {
            kind: HirExprKind::Integer(dim as i64),
            ty: TypeId::I64,
        };
        Ok(Some(HirExpr {
            kind: HirExprKind::GpuIntrinsic {
                intrinsic: kind,
                args: vec![dim_arg],
            },
            ty: TypeId::I64,
        }))
    }
}


#[cfg(test)]
mod some_record_payload_tests {
    use crate::hir::lower::tests::parse_and_lower;
    use crate::hir::types::{HirModule, HirStmt, HirType, TypeId};

    fn returned_type(module: &HirModule, name: &str) -> TypeId {
        module.functions.iter().find(|f| f.name == name).expect("fixture function")
            .body.iter().find_map(|statement| match statement {
                HirStmt::Return(Some(value)) => Some(value.ty),
                _ => None,
            }).expect("fixture return expression")
    }

    fn assert_nominal_record_binding(declaration: &str) {
        let source = format!(
            "{declaration} Record:\n    reducer: i64\n\nclass Decoy:\n    reducer: bool\n\nfn probe(value: Record) -> i64:\n    return match Some(value):\n        Some(owned): owned.reducer\n        nil: -1\n"
        );
        let module = parse_and_lower(&source).expect("Some(record variable) must lower with its nominal field owner");
        let probe = module.functions.iter().find(|f| f.name == "probe").expect("probe");
        let expected = probe.params.iter().find(|local| local.name == "value").expect("record input").ty;
        let owned = probe.locals.iter().find(|local| local.name == "owned").expect("payload binding");
        assert_eq!(owned.ty, expected, "Some payload must keep the input's exact nominal TypeId");
        assert!(matches!(module.types.get(owned.ty), Some(HirType::Struct { name, .. }) if name == "Record"),
            "payload owner must be Record, never the same-field Decoy: {:?}", module.types.get(owned.ty));
    }

    #[test]
    fn some_class_variable_retains_its_exact_nominal_payload_owner() {
        assert_nominal_record_binding("class");
    }

    #[test]
    fn some_struct_variable_retains_its_exact_nominal_payload_owner() {
        assert_nominal_record_binding("struct");
    }

    #[test]
    fn scalar_dynamic_and_array_payloads_keep_the_existing_erased_route() {
        for parameter in ["i64", "any", "[i64]"] {
            let source = format!("fn wrap(value: {parameter}) -> any:\n    return Some(value)\n");
            let module = parse_and_lower(&source).expect("unchanged Some fallback fixture");
            assert_eq!(returned_type(&module, "wrap"), TypeId::ANY,
                "non-record/function payload {parameter} must not acquire a nominal owner");
        }
    }

    #[test]
    fn existing_some_function_payload_keeps_its_function_binding() {
        let module = parse_and_lower(
            "fn wrap() -> any:\n    val callback = \\x: x + 1\n    return Some(callback)\n"
        ).expect("existing Some(function) route");
        let ty = returned_type(&module, "wrap");
        match module.types.get(ty) {
            Some(HirType::Enum { name, variants, type_bindings, .. }) => {
                assert_eq!(name, "Option");
                let payloads = variants.iter().find(|(variant, _)| variant == "Some")
                    .and_then(|(_, payload)| payload.as_ref()).expect("Some function payload");
                assert_eq!(payloads.len(), 1, "Some must retain exactly one function payload");
                let payload = payloads[0];
                assert!(matches!(module.types.get(payload), Some(HirType::Function { .. })));
                assert_eq!(type_bindings.get("T"), Some(&payload));
            }
            other => panic!("Some(function) lost its typed Option: {other:?}"),
        }
    }

    #[test]
    fn some_dynamic_payload_does_not_guess_an_unrelated_same_named_field_owner() {
        let source = "class Record:\n    reducer: i64\n\nclass Decoy:\n    reducer: bool\n\nfn probe(value: any) -> i64:\n    return match Some(value):\n        Some(owned): owned.reducer\n        nil: -1\n";
        let diagnostic = parse_and_lower(source).err()
            .expect("a dynamic payload must not bypass the ambiguous field-owner rejection")
            .to_string();
        assert!(diagnostic.contains("cannot infer field type")
            && diagnostic.contains("struct 'ANY'")
            && diagnostic.contains("field 'reducer'"),
            "expected the actual ambiguous dynamic-field diagnostic, got {diagnostic}");
    }
}
