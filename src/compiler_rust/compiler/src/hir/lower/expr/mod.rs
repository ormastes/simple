mod access;
mod calls;
mod collections;
mod contracts;
pub(crate) mod control;
mod helpers;
mod inference;
mod literals;
mod memory;
mod operators;
mod simd;
mod tensor;

use simple_parser::{self as ast, ast::ReferenceCapability, Expr};

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lenient_global_diag::LenientGlobalKind;
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;
use crate::value::BUILTIN_SPAWN;

impl Lowerer {
    fn builtin_numeric_method_result_type(&self, receiver_ty: TypeId, method: &str) -> Option<TypeId> {
        let is_numeric = matches!(
            receiver_ty,
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
        );
        if !is_numeric {
            return None;
        }

        match method {
            "to_string" | "to_text" => Some(TypeId::STRING),
            "to_int" | "to_i64" => Some(TypeId::I64),
            "to_i8" => Some(TypeId::I8),
            "to_i16" => Some(TypeId::I16),
            "to_i32" => Some(TypeId::I32),
            "to_u8" => Some(TypeId::U8),
            "to_u16" => Some(TypeId::U16),
            "to_u32" => Some(TypeId::U32),
            "to_u64" => Some(TypeId::U64),
            "to_f32" => Some(TypeId::F32),
            "to_float" | "to_f64" => Some(TypeId::F64),
            _ => None,
        }
    }

    fn enum_payload_type_for_builtin_method(&self, ty: TypeId) -> Option<TypeId> {
        match self.module.types.get(ty) {
            Some(HirType::Enum { variants, .. }) => variants
                .iter()
                .find_map(|(_, payload)| payload.as_ref().and_then(|fields| fields.first()).copied()),
            Some(HirType::Pointer { inner, .. }) => self.enum_payload_type_for_builtin_method(*inner),
            _ => None,
        }
    }

    fn enum_variant_payload_type_for_builtin_method(&self, ty: TypeId, variant_name: &str) -> Option<TypeId> {
        match self.module.types.get(ty) {
            Some(HirType::Enum { variants, .. }) => variants.iter().find_map(|(name, payload)| {
                if name == variant_name {
                    payload.as_ref().and_then(|fields| fields.first()).copied()
                } else {
                    None
                }
            }),
            Some(HirType::Pointer { inner, .. }) => {
                self.enum_variant_payload_type_for_builtin_method(*inner, variant_name)
            }
            _ => None,
        }
    }

    fn enum_has_variant_for_builtin_method(&self, ty: TypeId, variant_name: &str) -> bool {
        match self.module.types.get(ty) {
            Some(HirType::Enum { variants, .. }) => variants.iter().any(|(name, _)| name == variant_name),
            Some(HirType::Pointer { inner, .. }) => self.enum_has_variant_for_builtin_method(*inner, variant_name),
            _ => false,
        }
    }

    fn enum_variant_discriminant_for_builtin_method(&self, variant_name: &str) -> i64 {
        // Step (d), 2026-08-02: delegate to the SINGLE authoritative definition
        // in the runtime crate. This value is a RUNTIME ABI, not a
        // compiler-internal convention: `rt_option_some`/`rt_option_none`
        // (runtime/src/value/objects.rs) build Option values with it, the
        // bytecode compiler emits it into the instruction stream, and the
        // interpreter SFFI reads it back. A second copy here that drifted by
        // one character would desynchronize compiled code from the runtime
        // silently. See
        // doc/08_tracking/bug/enum_bare_name_collision_registry_2026-08-01.md.
        simple_runtime::value::hash_variant_discriminant(variant_name) as i64
    }

    /// Main expression lowering dispatcher
    ///
    /// This method delegates to specialized helper methods for each expression type,
    /// keeping the dispatch logic clean and maintainable.
    pub(in crate::hir::lower) fn lower_expr(&mut self, expr: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        match expr {
            Expr::Integer(_) | Expr::Float(_) | Expr::String(_) | Expr::Bool(_) | Expr::Nil => self.lower_literal(expr),
            Expr::TypedInteger(_, _) | Expr::TypedFloat(_, _) | Expr::TypedString(_, _) => {
                self.lower_typed_literal(expr)
            }
            Expr::FString { parts, type_meta } => self.lower_fstring(parts, type_meta, ctx),
            Expr::I18nString { name, default_text } => self.lower_i18n_string(name, default_text),
            Expr::I18nTemplate { name, parts, args } => self.lower_i18n_template(name, parts, args),
            Expr::I18nRef(name) => self.lower_i18n_ref(name),
            Expr::Identifier(name) => self.lower_identifier(name, ctx),
            Expr::Symbol(name) => {
                if ctx.lookup(name).is_some()
                    || self.globals.contains_key(name)
                    || self.named_callable_return_type(name).is_some()
                {
                    self.lower_identifier(name, ctx)
                } else {
                    Ok(HirExpr {
                        kind: HirExprKind::String(name.clone()),
                        ty: TypeId::STRING,
                    })
                }
            }
            Expr::Binary { op, left, right } => self.lower_binary(op, left, right, ctx),
            Expr::Unary { op, operand } => self.lower_unary(op, operand, ctx),
            Expr::Call { callee, args } => self.lower_call(callee, args, ctx),
            Expr::FieldAccess { receiver, field } => self.lower_field_access(receiver, field, ctx),
            Expr::TupleIndex { receiver, index } => self.lower_tuple_index(receiver, *index, ctx),
            Expr::Index { receiver, index } => self.lower_index(receiver, index, ctx),
            Expr::Slice {
                receiver,
                start,
                end,
                step,
            } => self.lower_slice(receiver, start.as_deref(), end.as_deref(), step.as_deref(), ctx),
            Expr::Tuple(exprs) => self.lower_tuple(exprs, ctx),
            Expr::LabeledTuple(fields) => self.lower_labeled_tuple(fields, ctx),
            Expr::Array(exprs) => self.lower_array(exprs, ctx),
            Expr::Dict(pairs) => self.lower_dict(pairs, ctx),
            Expr::ArrayRepeat { value, count } => self.lower_array_repeat(value, count, ctx),
            Expr::VecLiteral(exprs) => self.lower_vec_literal(exprs, ctx),
            Expr::If {
                let_pattern,
                condition,
                then_branch,
                else_branch,
            } => self.lower_if(
                let_pattern.as_ref(),
                condition,
                then_branch,
                else_branch.as_deref(),
                ctx,
            ),
            Expr::Lambda {
                params,
                body,
                capture_all,
                ..
            } => self.lower_lambda(params, body, *capture_all, ctx),
            Expr::Yield(value) => self.lower_yield(value.as_deref(), ctx),
            Expr::ContractResult => self.lower_contract_result(ctx),
            Expr::ContractOld(inner) => self.lower_contract_old(inner, ctx),
            Expr::New { kind, expr } => self.lower_new(kind, expr, ctx),
            Expr::MethodCall {
                receiver, method, args, ..
            } => self.lower_method_call(receiver, method, args, ctx),
            Expr::StructInit { name, fields, .. } => self.lower_struct_init(name, fields, ctx),
            // Simple Math: Grid and Tensor literals (#1920-#1929)
            Expr::GridLiteral { rows, device } => self.lower_grid_literal(rows, device, ctx),
            Expr::TensorLiteral {
                dtype,
                dims,
                mode,
                device,
            } => self.lower_tensor_literal(dtype, dims, mode, device, ctx),
            // Type cast expression: expr as Type
            Expr::Cast { expr, target_type } => self.lower_cast(expr, target_type, ctx),
            // Spawn expression: spawn expr
            Expr::Spawn(expr) => self.lower_spawn(expr, ctx),
            // Go expression: go(...) \params: or go \*:
            Expr::Go { args, params, body } => self.lower_go(args, params, body, ctx),
            // Path expression: Type.method - provide helpful error for .new()
            Expr::Path(segments) => self.lower_path(segments, ctx),
            // Match expression: match subject: case pattern: body
            Expr::Match { subject, arms } => self.lower_match(subject, arms, ctx),
            // Do block: do: statements... (block as expression)
            Expr::DoBlock(statements) => self.lower_do_block(statements, ctx),
            Expr::UnsafeBlock(statements) => self.lower_unsafe_block(statements, ctx),
            // Null coalescing: expr ?? default
            Expr::Coalesce { expr, default } => self.lower_coalesce(expr, default, ctx),
            // Existence check: expr.? (is present/non-empty)
            Expr::ExistsCheck(inner) => self.lower_exists_check(inner, ctx),
            // Await expression: await expr
            // Simple async is EAGER: await on a non-Future is the identity, so the
            // result type equals the operand type. No Future<T> representation exists
            // in the type system yet; when it does, extract T here.
            Expr::Await(inner) => {
                let future_hir = Box::new(self.lower_expr(inner, ctx)?);
                let operand_ty = future_hir.ty;
                Ok(HirExpr {
                    kind: HirExprKind::Await(future_hir),
                    ty: operand_ty,
                })
            }
            // Try expression: expr? - unwrap Result or propagate error
            Expr::Try(inner) => self.lower_try(inner, ctx),
            // Force unwrap: expr! - unwrap or panic (lowered same as try for codegen)
            Expr::ForceUnwrap(inner) => self.lower_try(inner, ctx),
            // Range expression: start..end or start..=end
            Expr::Range { start, end, bound } => self.lower_range(start.as_deref(), end.as_deref(), *bound, ctx),
            _ => {
                if self.lenient_types {
                    Ok(HirExpr {
                        kind: HirExprKind::Nil,
                        ty: TypeId::ANY,
                    })
                } else {
                    Err(LowerError::Unsupported(format!("{:?}", expr)))
                }
            }
        }
    }

    // ============================================================================
    // Identifier expressions
    // ============================================================================

    fn lower_identifier(&mut self, name: &str, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        // Handle "None" as alias for nil (Python compatibility)
        if name == "None" {
            return Ok(HirExpr {
                kind: HirExprKind::Nil,
                ty: TypeId::NIL,
            });
        }

        // Check if this is a contract binding (ret, err, result in postconditions)
        if ctx.is_postcondition_binding(name) {
            return Ok(HirExpr {
                kind: HirExprKind::ContractResult,
                ty: ctx.return_type,
            });
        }
        if ctx.is_error_binding(name) {
            // Error binding also refers to the return value (the error part)
            return Ok(HirExpr {
                kind: HirExprKind::ContractResult,
                ty: ctx.return_type,
            });
        }

        // Handle SFFI calls: @rt_function_name
        // The parser creates identifiers with @ prefix for SFFI calls
        // Look up the extern function without the @ prefix
        if let Some(stripped_name) = name.strip_prefix('@') {
            if let Some(ty) = self.globals.get(stripped_name).copied() {
                // Found extern function - return as global reference
                // The @ prefix is preserved in the name for debugging/tooling
                return Ok(HirExpr {
                    kind: HirExprKind::Global(name.to_string()),
                    ty,
                });
            } else if self.lenient_types {
                // Attributed: an unregistered `@extern` links against a weak
                // `return 0` stub instead of failing, so without this record
                // there is no signal of any kind.
                self.record_lenient_global(name, LenientGlobalKind::UnresolvedSffiExtern);
                return Ok(HirExpr {
                    kind: HirExprKind::Global(name.to_string()),
                    ty: TypeId::ANY,
                });
            } else {
                return Err(LowerError::UnknownVariable(format!(
                    "{} (SFFI call to undefined extern function '{}')",
                    name, stripped_name
                )));
            }
        }

        if let Some(idx) = ctx.lookup(name) {
            let ty = ctx.locals[idx].ty;
            Ok(HirExpr {
                kind: HirExprKind::Local(idx),
                ty,
            })
        } else if let Some((source, ty)) = self.resolve_import_alias(name).map(str::to_string).and_then(|source| {
            // Selective-import alias (`use m.{f as g}`): module flattening merged
            // the imported symbol in under its ORIGINAL name, so `g` names
            // nothing in the flattened unit and used to fall through to the
            // lenient-global path below -- an unresolved external symbol, which
            // is a silent whole-module JIT fallback (100-1000x) or a hard E1002
            // under AOT, where baremetal units (`cstart.spl`'s
            // `main as baremetal_main`) have no interpreter to fall back to.
            //
            // Ordered AFTER locals but BEFORE the callable/global lookups.
            //
            // It used to be the last attempt, on the reasoning that a same-named
            // callable or global should win. That is exactly what broke an alias
            // declared by the ENTRY module: unlike an imported module's, the
            // entry module's own `use` statement survives flattening, and
            // lowering registers a PHANTOM callable + global under the ALIAS
            // name from it. Those two branches then matched `g` and emitted
            // `Global("g")` -- a symbol nothing defines -- so every entry-module
            // `use m.{f as g}` reached codegen unresolved (measured: hard
            // `codegen: undefined symbol: g` under `compile --native`, silent
            // whole-module interpreter fallback under the JIT). Aliases used
            // from an IMPORTED module were unaffected, which is why the existing
            // check, whose alias lives in a mid module, stayed green.
            //
            // Shadowing a REAL declaration is prevented at the source instead:
            // `collect_flattened_import_aliases` refuses to record an alias
            // whose local name is declared anywhere in the flattened unit
            // (function, const, static or module-level let), so any entry that
            // reaches here provably names no real symbol of its own.
            let ty = self
                .named_callable_value_type(&source)
                .or_else(|| self.globals.get(&source).copied())?;
            Some((source, ty))
        }) {
            Ok(HirExpr {
                kind: HirExprKind::Global(source),
                ty,
            })
        } else if let Some(ty) = self.named_callable_value_type(name) {
            Ok(HirExpr {
                kind: HirExprKind::Global(name.to_string()),
                ty,
            })
        } else if let Some(ty) = self.globals.get(name).copied() {
            Ok(HirExpr {
                kind: HirExprKind::Global(name.to_string()),
                ty,
            })
        } else {
            // E1032 - Self in Static: Special case for 'self' not found
            if name == "self" && self.current_class_type.is_some() {
                if self.lenient_types {
                    // In lenient mode, treat self as a global with the class type
                    return Ok(HirExpr {
                        kind: HirExprKind::Global("self".to_string()),
                        ty: self.current_class_type.unwrap_or(TypeId::ANY),
                    });
                }
                // We're in a class method but self is not in scope = static method
                if let Some(func_name) = &self.current_function_name {
                    return Err(LowerError::Unsupported(format!(
                        "cannot use `self` in static method while lowering {func_name}"
                    )));
                }
                return Err(LowerError::SelfInStatic);
            }
            if self.lenient_types {
                // In lenient mode, treat unknown variables as globals with type ANY.
                //
                // This is the site that turns a typo or an HIR scope bug into a
                // link-time undefined symbol with no source location. The
                // fallback has to stay (cross-module names are legitimately
                // unresolvable while lowering one file at a time), so instead of
                // erroring we attribute it -- see `lenient_global_diag`.
                self.record_lenient_global(name, LenientGlobalKind::UnresolvedIdentifier);
                Ok(HirExpr {
                    kind: HirExprKind::Global(name.to_string()),
                    ty: TypeId::ANY,
                })
            } else {
                let detail = if let Some(func_name) = &self.current_function_name {
                    format!("{name} while lowering {func_name}")
                } else {
                    name.to_string()
                };
                Err(LowerError::UnknownVariable(detail))
            }
        }
    }

    // ============================================================================
    // Method calls (largest section - GPU/SIMD intrinsics)
    // ============================================================================

    fn looks_like_wrapper_static_member_sugar(member: &str) -> bool {
        member.chars().next().map(|ch| ch.is_ascii_uppercase()).unwrap_or(false)
    }

    fn wrapper_static_member_candidates(member: &str) -> Vec<String> {
        let mut candidates = Vec::new();
        let mut chars = member.chars();
        if let Some(first) = chars.next() {
            if first.is_ascii_uppercase() {
                let mut lower_first = String::with_capacity(member.len());
                lower_first.push(first.to_ascii_lowercase());
                lower_first.push_str(chars.as_str());
                if lower_first != member {
                    candidates.push(lower_first);
                }
            }
        }

        let lower_all = member.to_ascii_lowercase();
        if lower_all != member && !candidates.iter().any(|candidate| candidate == &lower_all) {
            candidates.push(lower_all);
        }

        candidates
    }

    fn static_member_return_type(&self, type_name: &str, member: &str) -> Option<TypeId> {
        let qualified = format!("{}.{}", type_name, member);
        self.method_return_types
            .get(&qualified)
            .copied()
            .or_else(|| {
                self.module
                    .functions
                    .iter()
                    .find(|function| function.name == qualified)
                    .map(|function| function.return_type)
            })
            .or_else(|| self.globals.get(&qualified).copied())
    }

    fn named_callable_return_type(&self, name: &str) -> Option<TypeId> {
        self.method_return_types
            .get(name)
            .copied()
            .or_else(|| self.globals.get(name).copied())
            .or_else(|| {
                self.resolve_function_alias(name).and_then(|target| {
                    self.method_return_types
                        .get(target)
                        .copied()
                        .or_else(|| self.globals.get(target).copied())
                })
            })
    }

    fn named_callable_value_type(&mut self, name: &str) -> Option<TypeId> {
        let target = self
            .resolve_function_alias(name)
            .map(str::to_string)
            .unwrap_or_else(|| name.to_string());
        if let Some(function) = self.module.functions.iter().find(|function| function.name == target) {
            return Some(self.module.types.register(HirType::Function {
                params: function.params.iter().map(|param| param.ty).collect(),
                ret: function.return_type,
            }));
        }

        match self.globals.get(&target).copied() {
            Some(ty) if matches!(self.module.types.get(ty), Some(HirType::Function { .. })) => Some(ty),
            _ => None,
        }
    }

    fn call_return_type(&self, callee: &Expr, fallback: TypeId) -> TypeId {
        if let Some(HirType::Function { ret, .. }) = self.module.types.get(fallback) {
            return *ret;
        }
        match callee {
            Expr::Identifier(name) => self.named_callable_return_type(name).unwrap_or(fallback),
            Expr::Path(segments) if segments.len() == 2 => self
                .static_member_return_type(&segments[0], &segments[1])
                .unwrap_or(fallback),
            _ => fallback,
        }
    }

    fn resolve_static_member_name(&self, type_name: &str, member: &str) -> Option<String> {
        if self.static_member_return_type(type_name, member).is_some() {
            return Some(member.to_string());
        }
        if !Self::looks_like_wrapper_static_member_sugar(member) {
            return None;
        }

        Self::wrapper_static_member_candidates(member)
            .into_iter()
            .find(|candidate| self.static_member_return_type(type_name, candidate).is_some())
    }

    fn static_enum_variant_type(&self, type_name: &str, member: &str) -> Option<TypeId> {
        let type_id = self
            .module
            .types
            .lookup(type_name)
            .or_else(|| self.globals.get(type_name).copied())?;
        match self.module.types.get(type_id) {
            Some(HirType::Enum { variants, .. }) if variants.iter().any(|(name, _)| name == member) => Some(type_id),
            _ => None,
        }
    }

    fn lower_static_enum_variant_call(
        &mut self,
        type_name: &str,
        member: &str,
        type_id: TypeId,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let args_hir = self.lower_call_args(args, ctx)?;
        Ok(HirExpr {
            kind: HirExprKind::Call {
                func: Box::new(HirExpr {
                    kind: HirExprKind::Global(format!("{}::{}", type_name, member)),
                    ty: type_id,
                }),
                args: args_hir,
            },
            ty: type_id,
        })
    }

    fn unknown_wrapper_static_member_error(&self, type_name: &str, member: &str) -> LowerError {
        let tried = Self::wrapper_static_member_candidates(member)
            .into_iter()
            .map(|candidate| format!("{}.{}", type_name, candidate))
            .collect::<Vec<_>>();

        let mut message = format!(
            "unknown static member '{}.{}'; wrapper-type static-member sugar only resolves to existing static methods",
            type_name, member
        );
        if !tried.is_empty() {
            message.push_str(&format!(" (tried: {})", tried.join(", ")));
        }

        LowerError::Unsupported(message)
    }

    pub(super) fn lower_static_member_call_with_sugar(
        &mut self,
        type_name: &str,
        member: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        if let Some(type_id) = self.static_enum_variant_type(type_name, member) {
            return self.lower_static_enum_variant_call(type_name, member, type_id, args, ctx);
        }
        if let Some(canonical_member) = self.resolve_static_member_name(type_name, member) {
            return self.lower_static_method_call(type_name, &canonical_member, args, ctx);
        }
        if member.chars().next().is_some_and(|ch| ch.is_ascii_uppercase()) {
            let args_hir = self.lower_call_args(args, ctx)?;
            return Ok(HirExpr {
                kind: HirExprKind::Call {
                    func: Box::new(HirExpr {
                        kind: HirExprKind::Global(format!("{}::{}", type_name, member)),
                        ty: TypeId::ANY,
                    }),
                    args: args_hir,
                },
                ty: TypeId::ANY,
            });
        }
        if Self::looks_like_wrapper_static_member_sugar(member) && !self.lenient_types {
            return Err(self.unknown_wrapper_static_member_error(type_name, member));
        }
        self.lower_static_method_call(type_name, member, args, ctx)
    }

    pub(super) fn try_lower_static_member_value_with_sugar(
        &mut self,
        type_name: &str,
        member: &str,
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        if !Self::looks_like_wrapper_static_member_sugar(member) {
            return Ok(None);
        }

        if let Some(canonical_member) = self.resolve_static_member_name(type_name, member) {
            return self
                .lower_static_method_call(type_name, &canonical_member, &[], ctx)
                .map(Some);
        }
        if member.chars().next().is_some_and(|ch| ch.is_ascii_uppercase()) {
            return Ok(Some(HirExpr {
                kind: HirExprKind::Global(format!("{}::{}", type_name, member)),
                ty: TypeId::ANY,
            }));
        }
        if self.lenient_types {
            return Ok(None);
        }

        Err(self.unknown_wrapper_static_member_error(type_name, member))
    }

    /// Classify a receiver TypeId for the text-index census.
    fn text_index_census_class(&self, ty: TypeId) -> &'static str {
        if ty == TypeId::STRING {
            return "TEXT";
        }
        if ty == TypeId::ANY {
            return "ANY";
        }
        match self.module.types.get(ty) {
            Some(HirType::String) => "TEXT",
            Some(HirType::Array { .. }) => "ARRAY",
            Some(HirType::Dict { .. }) => "DICT",
            Some(HirType::Tuple(_)) | Some(HirType::LabeledTuple(_)) => "TUPLE",
            Some(HirType::Simd { .. }) => "SIMD",
            Some(HirType::Any) => "ANY",
            Some(HirType::Void) => "VOID",
            Some(HirType::Pointer { inner, .. }) => {
                // One pointer-strip: `T?` / `&T` text receivers are common.
                let inner = *inner;
                if inner == TypeId::STRING
                    || matches!(self.module.types.get(inner), Some(HirType::String))
                {
                    "TEXT"
                } else {
                    "OTHER"
                }
            }
            Some(_) => "OTHER",
            None => "UNRESOLVED",
        }
    }

    /// Text-index CHARACTER-alignment census (Stage 1 tooling).
    ///
    /// Enabled by SIMPLE_TEXT_INDEX_CENSUS=1; silent and free otherwise.
    /// Emits one record per call site of an index-unit-sensitive primitive,
    /// CLASSIFIED BY RECEIVER TYPE, so the migration can be sized by
    /// text-typed sites instead of by grep -- `.len()` alone has ~122k
    /// syntactic hits that are overwhelmingly arrays/collections, and a
    /// measured corpus put ARRAY receivers ahead of TEXT 2.3 to 1.
    ///
    /// stdout, not eprint: native seed builds drop eprint, and this is a
    /// report stream rather than a diagnostic.
    /// See doc/03_plan/language/text_index_census_stage1_2026-07-30.md
    fn emit_text_index_census(&self, method: &str, recv_ty: TypeId) {
        const WATCHED: &[&str] = &[
            "len",
            "length",
            "index_of",
            "last_index_of",
            "slice",
            "substring",
            "char_at",
            "char_code_at",
            "byte_at",
            "bytes",
        ];
        if !WATCHED.contains(&method) {
            return;
        }
        if std::env::var("SIMPLE_TEXT_INDEX_CENSUS").is_err() {
            return;
        }
        let file = self
            .current_file
            .as_ref()
            .map(|p| p.display().to_string())
            .unwrap_or_else(|| "<unknown>".to_string());
        println!(
            "TEXTCENSUS\t{}\t{}\t{}",
            self.text_index_census_class(recv_ty),
            method,
            file
        );
    }

    fn lower_method_call(
        &mut self,
        receiver: &Expr,
        method: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Check for intrinsic calls on special identifiers
        if let Expr::Identifier(recv_name) = receiver {
            // Module imports are compile-time namespaces. Resolve the exact
            // qualified free-function owner before lowering the receiver;
            // lenient receiver lowering would otherwise create
            // Global("variables") and MIR GlobalLoad("variables").
            if ctx.lookup(recv_name).is_none() {
                let qualified = format!("{recv_name}.{method}");
                let resolved = self
                    .qualified_import_functions
                    .as_ref()
                    .and_then(|functions| functions.get(&qualified))
                    .cloned();
                if let Some(target) = resolved {
                    let args_hir = self.lower_call_args(args, ctx)?;
                    let ret_ty = self.named_callable_return_type(method).unwrap_or(TypeId::ANY);
                    return Ok(HirExpr {
                        kind: HirExprKind::Call {
                            func: Box::new(HirExpr {
                                kind: HirExprKind::Global(target),
                                ty: TypeId::ANY,
                            }),
                            args: args_hir,
                        },
                        ty: ret_ty,
                    });
                }
            }
            // this.* intrinsics
            if recv_name == "this" {
                if let Some(result) = self.lower_this_method(method, args)? {
                    return Ok(result);
                }
            }
            // thread_group.* intrinsics
            else if recv_name == "thread_group" {
                if let Some(result) = self.lower_thread_group_method(method, args)? {
                    return Ok(result);
                }
            }
            // gpu.* intrinsics
            else if recv_name == "gpu" {
                if let Some(result) = self.lower_gpu_method(method, args, ctx)? {
                    return Ok(result);
                }
            }
            // SIMD type static methods: f32x4.load(), f32x8.gather(), etc.
            else if self.is_simd_static_type_name(recv_name) {
                if let Some(result) = self.lower_simd_static_method(recv_name, method, args, ctx)? {
                    return Ok(result);
                }
            }
            // Static method calls on classes/structs
            // Only treat as static method if the name is NOT a local variable
            // (e.g., `text` is both a type alias and could be a variable name)
            // `Result`/`Option` are builtin generic enums: their instantiations are
            // registered unnamed (type_resolver `register()`), so `types.lookup`
            // misses them in modules that never lower the enum declaration itself
            // (e.g. freestanding/entry-closure kernel modules without the std
            // prelude). Without this, `Result.Ok(x)` degrades to a dynamic method
            // call on an unresolved global `Result` → rt_function_not_found → NIL.
            // Routing them through static-member lowering emits Global("Result::Ok")
            // which MIR canonicalizes to ResultOk/ResultErr/OptionSome/OptionNone.
            else if ctx.lookup(recv_name).is_none()
                && (self.module.types.lookup(recv_name).is_some() || recv_name == "Result" || recv_name == "Option")
            {
                if let Some(result) = self.lower_simd_static_method(recv_name, method, args, ctx)? {
                    return Ok(result);
                }
                return self.lower_static_member_call_with_sugar(recv_name, method, args, ctx);
            }
        }

        // Check for SIMD vector instance methods
        let receiver_hir = self.lower_expr(receiver, ctx)?;

        // Stage 1 census hook: placed immediately after the receiver is
        // lowered, BEFORE the builtin/string-method dispatch below
        // early-returns, so no watched primitive escapes the count.
        self.emit_text_index_census(method, receiver_hir.ty);
        if let Some(HirType::Simd { .. }) = self.module.types.get(receiver_hir.ty) {
            if let Some(result) = self.lower_simd_instance_method(&receiver_hir, method, args, ctx)? {
                return Ok(result);
            }
        }

        // Check for builtin collection/string methods
        if let Some(result) = self.lower_builtin_method_call(&receiver_hir, method, args, ctx)? {
            return Ok(result);
        }

        // Lower arguments for generic method call
        let hir_args = self.lower_call_args(args, ctx)?;

        if (method == "append" || method == "push") && hir_args.len() == 1 {
            if let HirExprKind::Local(local_idx) = receiver_hir.kind {
                if let Some(HirType::Array { element, size }) = self.module.types.get(receiver_hir.ty).cloned() {
                    if element == self.type_inference_config.empty_array_default && size == Some(0) {
                        let refined_ty = self.module.types.register(HirType::Array {
                            element: hir_args[0].ty,
                            size,
                        });
                        if let Some(local) = ctx.locals.get_mut(local_idx) {
                            local.ty = refined_ty;
                        }
                    }
                }
            }
        }

        // Look up return type from module functions
        let recv_ty = receiver_hir.ty;
        let return_ty = self.lookup_method_return_type(recv_ty, method);

        // Generate generic method call for user-defined methods
        // Uses dynamic dispatch since we don't know the concrete type at compile time
        Ok(HirExpr {
            kind: HirExprKind::MethodCall {
                receiver: Box::new(receiver_hir),
                method: method.to_string(),
                args: hir_args,
                dispatch: DispatchMode::Dynamic,
            },
            ty: return_ty,
        })
    }

    /// Look up the return type of a method from pre-registered signatures.
    fn lookup_method_return_type(&self, recv_ty: TypeId, method: &str) -> TypeId {
        // Optional unwrap: `T?` is represented as `Pointer { inner: T }`
        // (type_resolver.rs). `.unwrap()`/`.expect(...)` on such a value yields
        // the inner `T`. Genuine `Option<T>`/`Result<T,E>` enum cases are already
        // consumed by `lower_builtin_method_call` before this fall-through, so the
        // only remaining unwrap target whose type is otherwise ANY is the nullable
        // pointer. Type-only upgrade (the call stays a dynamic MethodCall); a
        // struct inner lets `parsed.field` lower to a FieldGet instead of crashing
        // with "struct 'ANY' field 'X'".
        if matches!(method, "unwrap" | "expect") {
            if let Some(HirType::Pointer { inner, .. }) = self.module.types.get(recv_ty) {
                return *inner;
            }
        }
        if recv_ty != TypeId::ANY && recv_ty != TypeId::VOID {
            if let Some(HirType::Struct { fields, .. }) = self.module.types.get(recv_ty) {
                if let Some((_, field_ty)) = fields.iter().find(|(field_name, _)| field_name == method) {
                    if let Some(HirType::Function { ret, .. }) = self.module.types.get(*field_ty) {
                        return *ret;
                    }
                }
            }
        }
        // If receiver type is known, look up "TypeName.method"
        if recv_ty != TypeId::ANY && recv_ty != TypeId::VOID {
            if let Some(hir_ty) = self.module.types.get(recv_ty) {
                let type_name = match hir_ty {
                    HirType::Struct { name, .. } => Some(name.as_str()),
                    HirType::Enum { name, .. } => Some(name.as_str()),
                    _ => None,
                };
                if let Some(name) = type_name {
                    let qualified = format!("{}.{}", name, method);
                    if let Some(&ret_ty) = self.method_return_types.get(&qualified) {
                        return ret_ty;
                    }
                }
            }
        }
        // Search pre-registered methods for ".method" suffix
        // Sort matches by name length (shortest = most specific) for deterministic resolution
        let suffix = format!(".{}", method);
        // Trait names intentionally alias to ANY in HIR because calls use a
        // runtime vtable.  A module that imports only the trait therefore has
        // no `ConcreteType.method` entry in `method_return_types`; the trait
        // signature is the only authoritative result type.  Consult it before
        // the implementation-name fallback whenever all matching trait
        // signatures agree.  This is especially important for `T?` returns:
        // losing `MouseEvent?` here makes `if val event = backend.poll_mouse()`
        // bind `event` as ANY and rejects every subsequent field access.
        if recv_ty == TypeId::ANY {
            let mut trait_return: Option<TypeId> = None;
            let mut traits_disagree = false;
            for trait_info in self.module.trait_infos.values() {
                let Some(sig) = trait_info.methods.get(method) else {
                    continue;
                };
                if sig.return_type == TypeId::ANY || sig.return_type == TypeId::VOID {
                    continue;
                }
                match trait_return {
                    None => trait_return = Some(sig.return_type),
                    Some(previous) if previous != sig.return_type => {
                        traits_disagree = true;
                        break;
                    }
                    _ => {}
                }
            }
            if !traits_disagree {
                if let Some(return_type) = trait_return {
                    return return_type;
                }
            }
        }
        // When the impl matches DISAGREE on the return type, the shortest-name
        // tiebreak below is unreliable: e.g. for `core.read_pixels()` on a
        // trait-typed (ANY-aliased) `RenderBackend` receiver, an FFI wrapper's
        // `RocmFfi.read_pixels -> Bool` outranked 16 backends returning `[u32]`
        // purely by name length, so `fb` was typed `Bool` and indexing it
        // failed → whole-module JIT fallback. For a trait-typed receiver the
        // trait interface is authoritative, so prefer the trait method's
        // declared return type when the impls conflict.
        let mut seen_ret: Option<TypeId> = None;
        let mut impls_disagree = false;
        for (_, &rt) in self
            .method_return_types
            .iter()
            .filter(|(name, _)| name.ends_with(&suffix))
        {
            match seen_ret {
                None => seen_ret = Some(rt),
                Some(prev) if prev != rt => {
                    impls_disagree = true;
                    break;
                }
                _ => {}
            }
        }
        if impls_disagree {
            let mut trait_names: Vec<&String> = self.module.trait_infos.keys().collect();
            trait_names.sort();
            for tn in trait_names {
                if let Some(sig) = self.module.trait_infos.get(tn).and_then(|ti| ti.methods.get(method)) {
                    if sig.return_type != TypeId::ANY && sig.return_type != TypeId::VOID {
                        return sig.return_type;
                    }
                }
            }
        }
        if let Some((_, &ret_ty)) = self
            .method_return_types
            .iter()
            .filter(|(name, _)| name.ends_with(&suffix))
            .min_by_key(|(name, _)| name.len())
        {
            return ret_ty;
        }
        // Builtin string methods that return a RAW native i64 (a code point /
        // hash), not a tagged RuntimeValue. Without this they fall through to
        // ANY, and `s.char_code_at(i) as u8` then lowers to an ANY->int Cast
        // that calls rt_value_as_int (a tag-aware unbox): a raw code point whose
        // low 3 bits are 0 (any codepoint ≡ 0 mod 8, e.g. 'X'=88, 'H'=72) gets
        // shifted `>>3` and silently corrupts (88->11). Typing them I64 makes
        // the cast a plain narrow. See
        // doc/08_tracking/bug/native_char_code_at_tag_shift_2026-07-19.md.
        // Only applies as a last-resort fallback (a genuine user method of the
        // same name matched above), and only on a string/erased receiver.
        if matches!(method, "char_code_at" | "byte_at" | "ord" | "codepoint" | "code_point" | "hash")
            && (recv_ty == TypeId::STRING || recv_ty == TypeId::ANY)
        {
            return TypeId::I64;
        }
        // Builtin string->float parse methods (`to_float`/`to_f64`) are compiler
        // intrinsics with no registered `method_return_types` entry (they are not
        // real user-defined methods), so without this they fall through to ANY
        // just like `char_code_at` above — except the raw native RETURN VALUE is
        // an f64 bit pattern, not a tagged RuntimeValue. Downstream code (e.g.
        // MIR lowering's `needs_float_boxing` in lowering_expr_method.rs) already
        // boxes an F64-typed receiver correctly via BoxFloat/rt_value_float
        // before passing it to a chained call like `.to_string()`; it just never
        // fires because the receiver was mistyped ANY. Typing them F64 here
        // makes that existing boxing logic take effect. See float print bug
        // (lane FLOATBOX, 2026-07-29): `s.to_float().to_string()` printed the
        // raw f64 bit pattern as an int under JIT.
        if matches!(method, "to_float" | "to_f64") && (recv_ty == TypeId::STRING || recv_ty == TypeId::ANY) {
            return TypeId::F64;
        }
        // Builtin float MATH methods on a float receiver. Exactly the same
        // mechanism as the `to_float`/`to_f64` case directly above, one layer
        // over: these are compiler intrinsics lowered inline by
        // `codegen/instr/methods.rs` (`matches!(method, "sqrt" | "abs" |
        // "floor" | "ceil" | "round")` -> `builder.ins().sqrt/fabs/floor/
        // ceil/nearest`), so they have no `method_return_types` entry and fell
        // through to ANY here. The instruction produces a RAW unboxed f64, and
        // an ANY-typed expression is assumed to be an already-tagged
        // RuntimeValue, so MIR's print lowering
        // (`needs_float_boxing = matches!(arg.ty, F32 | F64)` in
        // mir/lower/lowering_expr_builtin.rs) emitted no BoxFloat and
        // `rt_print_value` applied `as_int()` (`raw >> 3`) to the IEEE bit
        // pattern:
        //     val b: f64 = 16.0
        //     print b.sqrt()          -> 577023702256844800 == bits(4.0) / 8
        //     val c: f64 = b.sqrt()
        //     print c                 -> 4.0
        // The typed-local form was correct because the DECLARED local type
        // supplied the F64 the expression type lacked -- which is exactly what
        // isolated this to the type stamp rather than the computation. Typing
        // the call as the receiver's float type makes the existing boxing fire.
        // The list is deliberately the codegen inline set and nothing more:
        // `trunc`/`sin`/`pow`/`min`/`max` on an f64 receiver are not
        // implemented at all today ("Function 'f64.sin' not found"), and
        // stamping F64 on a method that actually returns a tagged value would
        // double-box it. Restricted to float receivers so integer `abs` keeps
        // returning an integer.
        // doc/08_tracking/bug/float_returning_method_in_argument_position_prints_tagged_bits_2026-08-10.md
        //
        // Extended 2026-08-11 to the remaining float math methods now given a
        // real lowering in `codegen/instr/methods.rs`
        // (`sin`/`cos`/`tan`/`asin`/`acos`/`atan`/`sinh`/`cosh`/`tanh`/`exp`/
        // `ln`/`log2`/`log10`/`cbrt`/`trunc` via the `rt_math_*` runtime ABI,
        // `pow`/`max`/`min` likewise). Without a real return-type stamp here
        // these stayed `ANY`, which routes the call through fully dynamic
        // by-name dispatch instead of the static codegen path — the dynamic
        // resolver has no entry named e.g. `f64.sin`, so it failed with
        // `Function 'f64.sin' not found` even though the codegen lowering now
        // exists. See
        // doc/08_tracking/bug/float_and_int_math_methods_missing_on_numeric_receivers_2026-08-10.md.
        if matches!(
            method,
            "sqrt"
                | "abs"
                | "floor"
                | "ceil"
                | "round"
                | "trunc"
                | "sin"
                | "cos"
                | "tan"
                | "asin"
                | "acos"
                | "atan"
                | "sinh"
                | "cosh"
                | "tanh"
                | "exp"
                | "ln"
                | "log2"
                | "log10"
                | "cbrt"
                | "pow"
                | "powf"
                | "max"
                | "min"
        ) && matches!(recv_ty, TypeId::F32 | TypeId::F64)
        {
            return recv_ty;
        }
        // Integer `.abs()` now has a real codegen lowering too (native
        // Cranelift `iabs`); stamp it I64/I32/etc so it takes the static path
        // instead of dynamic by-name dispatch (`Function 'i64.abs' not found`).
        if method == "abs"
            && matches!(
                recv_ty,
                TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64
            )
        {
            return recv_ty;
        }
        TypeId::ANY
    }

    /// Handle this.index(), this.thread_index(), this.group_index()
    fn lower_this_method(&self, method: &str, args: &[ast::Argument]) -> LowerResult<Option<HirExpr>> {
        if !args.is_empty() {
            return Err(LowerError::Unsupported(format!("this.{}() takes no arguments", method)));
        }

        let intrinsic = match method {
            "index" => GpuIntrinsicKind::SimdIndex,
            "thread_index" => GpuIntrinsicKind::SimdThreadIndex,
            "group_index" => GpuIntrinsicKind::SimdGroupIndex,
            _ => return Ok(None),
        };

        Ok(Some(HirExpr {
            kind: HirExprKind::GpuIntrinsic {
                intrinsic,
                args: vec![],
            },
            ty: TypeId::I64,
        }))
    }

    /// Handle thread_group.barrier()
    fn lower_thread_group_method(&self, method: &str, args: &[ast::Argument]) -> LowerResult<Option<HirExpr>> {
        if method != "barrier" {
            return Err(LowerError::Unsupported(format!(
                "unknown thread_group method: {}",
                method
            )));
        }

        if !args.is_empty() {
            return Err(LowerError::Unsupported(
                "thread_group.barrier() takes no arguments".to_string(),
            ));
        }

        Ok(Some(HirExpr {
            kind: HirExprKind::GpuIntrinsic {
                intrinsic: GpuIntrinsicKind::Barrier,
                args: vec![],
            },
            ty: TypeId::VOID,
        }))
    }

    /// Handle builtin method calls on strings, arrays
    fn lower_builtin_method_call(
        &mut self,
        receiver: &HirExpr,
        method: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        let mut receiver = receiver.clone();
        let hir_args = self.lower_call_args(args, ctx)?;

        if matches!(method, "push" | "append") && hir_args.len() == 1 {
            if let HirExprKind::Local(local_index) = receiver.kind {
                if self.untyped_empty_array_locals.remove(&local_index) {
                    let specialized_array_ty = self.module.types.register(HirType::Array {
                        element: hir_args[0].ty,
                        size: None,
                    });
                    if let Some(local) = ctx.locals.get_mut(local_index) {
                        local.ty = specialized_array_ty;
                    }
                    receiver.ty = specialized_array_ty;
                }
            }
        }

        if args.is_empty() {
            match method {
                "unwrap" => {
                    if let Some(payload_ty) = self.enum_payload_type_for_builtin_method(receiver.ty) {
                        return Ok(Some(HirExpr {
                            kind: HirExprKind::BuiltinCall {
                                name: "rt_enum_payload".to_string(),
                                args: vec![receiver.clone()],
                            },
                            ty: payload_ty,
                        }));
                    }
                }
                "unwrap_err" => {
                    if let Some(payload_ty) = self.enum_variant_payload_type_for_builtin_method(receiver.ty, "Err") {
                        return Ok(Some(HirExpr {
                            kind: HirExprKind::BuiltinCall {
                                name: "rt_enum_payload".to_string(),
                                args: vec![receiver.clone()],
                            },
                            ty: payload_ty,
                        }));
                    }
                }
                "is_some"
                    if matches!(receiver.ty, TypeId::ANY | TypeId::NIL)
                        || self.enum_has_variant_for_builtin_method(receiver.ty, "Some") =>
                {
                    return Ok(Some(HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: "rt_is_some".to_string(),
                            args: vec![receiver.clone()],
                        },
                        ty: TypeId::BOOL,
                    }));
                }
                "is_none"
                    if matches!(receiver.ty, TypeId::ANY | TypeId::NIL)
                        || self.enum_has_variant_for_builtin_method(receiver.ty, "None") =>
                {
                    return Ok(Some(HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: "rt_is_none".to_string(),
                            args: vec![receiver.clone()],
                        },
                        ty: TypeId::BOOL,
                    }));
                }
                "is_ok"
                    if matches!(receiver.ty, TypeId::ANY | TypeId::NIL)
                        || self.enum_has_variant_for_builtin_method(receiver.ty, "Ok") =>
                {
                    return Ok(Some(HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: "rt_enum_check_discriminant".to_string(),
                            args: vec![
                                receiver.clone(),
                                HirExpr {
                                    kind: HirExprKind::Integer(self.enum_variant_discriminant_for_builtin_method("Ok")),
                                    ty: TypeId::I64,
                                },
                            ],
                        },
                        ty: TypeId::BOOL,
                    }));
                }
                "is_err"
                    if matches!(receiver.ty, TypeId::ANY | TypeId::NIL)
                        || self.enum_has_variant_for_builtin_method(receiver.ty, "Err") =>
                {
                    return Ok(Some(HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: "rt_enum_check_discriminant".to_string(),
                            args: vec![
                                receiver.clone(),
                                HirExpr {
                                    kind: HirExprKind::Integer(
                                        self.enum_variant_discriminant_for_builtin_method("Err"),
                                    ),
                                    ty: TypeId::I64,
                                },
                            ],
                        },
                        ty: TypeId::BOOL,
                    }));
                }
                _ => {}
            }
        }

        let is_string = matches!(self.module.types.get(receiver.ty), Some(HirType::String));
        let is_array = matches!(self.module.types.get(receiver.ty), Some(HirType::Array { .. }));

        if let Some(ty) = self.builtin_numeric_method_result_type(receiver.ty, method) {
            return Ok(Some(HirExpr {
                kind: HirExprKind::MethodCall {
                    receiver: Box::new(receiver.clone()),
                    method: method.to_string(),
                    args: hir_args,
                    dispatch: DispatchMode::Static,
                },
                ty,
            }));
        }

        // String methods
        if is_string {
            let result_ty = match method {
                // "length" is a documented synonym of "len" (see codegen's
                // "len" | "length" => "rt_len" tables in
                // codegen/instr/{methods,calls,closures_structs}.rs and the
                // interpreter's method_dispatch.rs / string.rs). This table
                // is the ONLY place that recognizes "len" but forgot
                // "length" — so `.length()` fell through to generic dynamic
                // dispatch typed TypeId::ANY, which skips the int-boxing
                // step at the print()/call-arg lowering site (see
                // lowering_expr_builtin.rs `needs_int_boxing`), yielding a
                // raw untagged i64 fed straight into rt_println_value —
                // silently misdecoded as 0.0 (bug
                // jit_string_length_var_control_flow_wrong_value_2026-07-17.md).
                "len" | "length" => Some(TypeId::I64),
                // `s.is_empty()` (interpreter_method/string.rs "is_empty")
                // returns a raw i64 0/1 from `rt_is_empty`/equivalent — same
                // "raw i64 needs BoxInt/BoxBool before generic print/use" gap
                // class as `"length"` above. This table had `is_empty` for
                // arrays/dicts (below) but NOT for strings, so `s.is_empty()`
                // fell through to generic dynamic dispatch typed TypeId::ANY,
                // which skipped the bool-boxing step at the print()/call-arg
                // lowering site — printing the raw untagged int (`0`) instead
                // of `false`, and misdecoding the truthy case as `nil`
                // (bug jit_bool_result_type_gap_2026-07-29, lane BOOLRESULT).
                // The `is_*` character-class predicates return bool too, and
                // omitting them reproduced this bug exactly: `"123".is_digit()`
                // printed `nil` (truthy misdecoded) and `"12a".is_digit()`
                // printed `0` instead of `false`, even though the runtime
                // function was correctly wired at all seven other sites. A
                // dispatch entry alone is not enough for a bool-returning
                // method -- the result type must be declared here or the
                // bool-boxing step is skipped.
                "starts_with" | "ends_with" | "contains" | "is_empty" | "is_digit" | "is_numeric" | "is_alpha"
                | "is_alphabetic" | "is_alphanumeric" | "is_alnum" | "is_whitespace" => Some(TypeId::BOOL),
                "concat" | "slice" | "substring" | "replace" | "trim" | "trim_start" | "trim_end" | "lower"
                | "to_lower" | "upper" | "to_upper" => Some(TypeId::STRING),
                // `appended`/`prepended` (= `concat` with swapped operand
                // order) return a fresh String — same shape as the
                // `concat`/`slice` entry just above. See the MIR expansion
                // in lowering_expr_method.rs (lane BATCH3). NOTE: `substr`/
                // `take` were deliberately NOT added here at first — `rt_slice`'s
                // string branch is byte-indexed while the interpreter is
                // char-indexed, a silent JIT-vs-interpreter divergence on
                // multi-byte UTF-8 receivers, so those two were reclassified
                // NEEDS-RUNTIME (need a char-aware slice symbol) rather than
                // CLEAN-LOWERING. `substr` now HAS that char-aware symbol
                // (`rt_string_substr`/`rt_string_substr_from`) and is listed
                // below; `take` is still open because it is also an array
                // method and needs receiver dispatch.
                "appended" | "prepended" => Some(TypeId::STRING),
                // Newly wired text methods (see calls.rs and
                // runtime/src/value/collections.rs). `char_count` returns a raw
                // i64 and the rest return a fresh String; both classes need
                // their result type declared here or the boxing step at the
                // print()/call-arg lowering site is skipped, exactly as it was
                // for `length` and the `is_*` predicates above.
                "char_count" => Some(TypeId::I64),
                "capitalize" | "swapcase" | "title" | "titlecase" | "chomp" | "trim_start_matches"
                | "trim_end_matches" | "removeprefix" | "remove_prefix" | "removesuffix" | "remove_suffix"
                | "squeeze" | "replace_first" | "push_str" | "pad_left" | "pad_start" | "pad_right" | "pad_end"
                | "center" | "zfill" | "substr" | "rev" | "reversed" | "sorted" | "take" | "taken" | "drop"
                | "dropped" | "skip" => Some(TypeId::STRING),
                // `partition`/`rpartition` return [before, separator, after].
                "partition" | "rpartition" => Some(
                    self.module
                        .types
                        .register(HirType::Array { element: TypeId::STRING, size: None }),
                ),
                // `find_all`/`find_indices` return an array of BYTE offsets,
                // the same shape as `.bytes()`.
                "find_all" | "find_indices" => Some(
                    self.module
                        .types
                        .register(HirType::Array { element: TypeId::I64, size: None }),
                ),
                "split" => Some(
                    self.module
                        .types
                        .register(HirType::Array { element: TypeId::STRING, size: None }),
                ),
                // One `chars()` element is a one-codepoint String in both the
                // interpreter and `rt_string_chars`.  Keep that element type
                // precise so indexing the result remains a String receiver;
                // otherwise a following text builtin (for example
                // `s.chars()[0].char_code_at(0)`) is lowered from ANY and can
                // be stolen by an unrelated custom method owner.
                "chars" => Some(
                    self.module
                        .types
                        .register(HirType::Array { element: TypeId::STRING, size: None }),
                ),
                // `.lines()` / `.split_lines()` had NO codegen mapping at all
                // until `rt_string_lines` was added alongside the sibling
                // `rt_string_bytes`/`rt_string_chars` unary string->array
                // runtime helpers, so every compiled call failed at runtime
                // with `Function 'str.lines' not found` and the nil result made
                // `.len()` report `-1`. That `-1` is the ordinary "len of a nil
                // receiver" answer, NOT the `Dict.len()` native sentinel.
                "lines" | "split_lines" => Some(
                    self.module
                        .types
                        .register(HirType::Array { element: TypeId::STRING, size: None }),
                ),
                // find/rfind return -1 if not found, position if found (raw i64 from rt_string_find)
                "find" | "index_of" | "find_str" | "rfind" | "last_index_of" => Some(TypeId::I64),
                // `s.count(needle)` (interpreter_method/string.rs "count") is
                // `s.matches(&needle).count()`, a raw i64 — same "raw i64
                // needs BoxInt before generic print/use" gap class as
                // `index_of` above. The MIR lowering (lowering_expr_method.rs,
                // task: jit_method_dispatch_audit_2026-07-29) expands this to
                // `split(needle).len() - 1` (no `rt_string_count` runtime
                // symbol exists); see that file for the documented
                // empty-needle edge-case divergence.
                "count" => Some(TypeId::I64),
                // `.bytes()` returns UTF-8 bytes as an array of ints (see
                // interpreter_method/string.rs `"bytes" => Vec<Value::Int>`,
                // and the native runtime's `rt_string_bytes`, which pushes
                // `RuntimeValue::from_int(b as i64)` per byte). This table
                // forgetting `"bytes"` is the SAME class of gap as the
                // `"length"` alias above: `.bytes()` fell through to generic
                // dynamic dispatch typed `TypeId::ANY`, so `byte_arr[idx]`
                // never got the `UnboxInt` MIR instruction that's gated on a
                // known int element type
                // (mir/lower/lowering_expr_struct.rs `needs_int_unbox`),
                // leaving each element as a raw tagged `RuntimeValue`
                // (`(v << 3) | TAG_INT`) that downstream relational ops
                // (`<`, `<=`, `>`, `>=`) and arithmetic (`+`, `-`) compiled as
                // raw native ops assuming an already-unboxed i64 — corrupting
                // results (bug
                // seed_interp_bytes_u8_relational_boxtag_shift_2026-07-17.md;
                // marker: seed_bytes_u8_boxtag_2026-07-17).
                "bytes" => Some(
                    self.module
                        .types
                        .register(HirType::Array { element: TypeId::I64, size: None }),
                ),
                // `parse_int` and its `to_int`/`to_i64` aliases all lower to the
                // runtime's `rt_string_to_int`, which returns a RAW (untagged)
                // i64 — see the identical
                // `"to_int" | "to_i64" | "parse_int" => "rt_string_to_int"`
                // arms in codegen/instr/calls.rs, codegen/instr/closures_structs.rs,
                // codegen/llvm/emitter.rs and codegen/llvm/functions{,/calls}.rs.
                // This table forgetting them is the SAME class of gap as the
                // `"length"` and `"bytes"` entries above: the call fell through
                // to generic dynamic dispatch typed `TypeId::ANY`, so MIR
                // emitted no int-boxing and the raw i64 was handed to
                // `rt_println_value`, which then decoded it BY BIT PATTERN
                // rather than by value. The parse itself was always correct —
                // only the decode was wrong, which is why the symptom looked
                // like a float: `"42"` printed as the f64 denormal of bit
                // pattern 42 (`0.000…0002`) and `"-7"` printed as
                // `<invalid-heap:0xfffffffffffffff9>` (raw -7 read as a
                // pointer), while `"0"` happened to be right because bit
                // pattern 0 decodes to 0.
                //
                // SPLIT (2026-08-17): `to_int`/`to_i64` are TOTAL — specified to
                // yield `0` on failure — so `TypeId::I64` is right for them and
                // they keep the bare-i64 `rt_string_to_int`. The `parse_*`
                // family is NOT total: it returns `Option`. Typing it `I64`
                // here erased that Option at the type level, which is why
                // `"42".parse_int()` evaluated to the plain integer `42` and
                // `.is_some()` on it died with `Function 'i64.is_some' not
                // found`. It now takes `TypeId::ANY` and the tagged
                // `rt_string_parse_int` (NIL on failure), exactly mirroring the
                // `parse_f64`/`parse_float` family below, which was already
                // ANY-typed and already behaved correctly — that working twin
                // is the template this follows rather than a new invention.
                // See doc/08_tracking/bug/parse_family_strips_option_jit_native_2026-08-02.md
                "to_int" | "to_i64" => Some(TypeId::I64),
                "parse_int" | "parse_i32" | "parse_i64" => Some(TypeId::ANY),
                _ => None,
            };

            if let Some(ty) = result_ty {
                return Ok(Some(HirExpr {
                    kind: HirExprKind::MethodCall {
                        receiver: Box::new(receiver.clone()),
                        method: method.to_string(),
                        args: hir_args,
                        dispatch: DispatchMode::Static,
                    },
                    ty,
                }));
            }
        }

        // Array methods
        if is_array {
            let result_ty = match method {
                // "length" synonym — see the string-methods comment above.
                "len" | "length" => Some(TypeId::I64),
                "push" => Some(receiver.ty), // Returns the new array (same type)
                "clear" => Some(TypeId::VOID),
                // `pop` and `remove(index)` both yield the ELEMENT, so both take
                // the element type. `remove` was MISSING from this table, which
                // is the same gap class documented for `index_of` and `sum`
                // below: the call fell through to generic dynamic dispatch typed
                // `TypeId::ANY`, so no unboxing was emitted on the result and the
                // still-TAGGED element reached the caller. Measured on
                // `self.items.remove(0)` over `[7, 8, 9]` typed `[i64]`: `56`,
                // i.e. 7 << 3 — the element's value multiplied by 8, the
                // signature of a tag that was never stripped. `pop` was correct
                // purely because it is listed here.
                // doc/08_tracking/bug/array_remove_returns_mutated_array_not_removed_element_2026-07-20.md
                "pop" | "remove" => {
                    if let Some(HirType::Array { element, .. }) = self.module.types.get(receiver.ty) {
                        Some(*element)
                    } else {
                        Some(TypeId::ANY)
                    }
                }
                "contains" | "is_empty" => Some(TypeId::BOOL),
                // `[T].index_of(v)` returns a raw i64 position (-1 when absent),
                // exactly like the string table's `index_of` above. This table
                // omitting it is the SAME class of gap as `"length"`/`"bytes"`:
                // the call fell through to generic dynamic dispatch typed
                // TypeId::ANY, so MIR emitted NO `BoxInt` on the result — the
                // raw i64 was then handed to `to_string`/`print` as if it were
                // an already-tagged RuntimeValue and misdecoded by its bit
                // pattern (0 -> "0", 1 -> "nil", 2 -> "0.0", -1 ->
                // "<value:0xffffffffffffffff>"). Typing it I64 restores the
                // BoxInt and picks static dispatch, which codegen already
                // routes to `rt_index_of`.
                "index_of" => Some(TypeId::I64),
                // `arr.sum()` (interpreter_method/collections.rs "sum") only
                // accumulates Int elements and always returns an Int — same
                // "raw i64 needs BoxInt" gap class as `index_of` above. The
                // MIR lowering (lowering_expr_method.rs, task:
                // jit_method_dispatch_audit_2026-07-29) unboxes
                // `rt_array_sum`'s tag-boxed result to match this type.
                "sum" => Some(TypeId::I64),
                "join" => Some(TypeId::STRING),
                "slice" | "filter" | "map" => Some(receiver.ty), // Returns same array type
                // `arr.take(n)` / `arr.skip(n)` / `arr.drop(n)` all return a
                // NEW array of the same element type, clamped to [0, len] —
                // same shape as `slice`/`filter`/`map` above. `arr.insert(i,
                // v)` also always returns a new array (or an unchanged copy
                // when `i` is out of range) — see the MIR expansion in
                // lowering_expr_method.rs.
                "take" | "skip" | "drop" | "insert" => Some(receiver.ty),
                // `[T].at(i)` is the bounds-checked accessor and is the ONE
                // array method here whose result is genuinely optional, so it
                // types as `T?` (`HirType::Pointer`) rather than bare `T`.
                //
                // This is load-bearing, not cosmetic. `case Some(v)` desugars to
                // a `rt_enum_payload` builtin call whose HIR type decides
                // whether MIR emits `UnboxInt` (lowering_expr_builtin.rs: the
                // `needs_int_unbox` gate fires only for a concrete scalar
                // TypeId). The payload recovery in
                // `get_enum_variant_field_types_with_hint` only reaches `T`
                // when the subject is `HirType::Pointer { inner }`. With `at`
                // missing from this table the subject was `TypeId::ANY`, the
                // binding type was `ANY`, no `UnboxInt` was emitted, and the
                // bound value stayed tag-boxed — `xs.at(0)` on `[10, ...]`
                // bound `v = 80` (10 << 3) instead of `10`.
                //
                // See doc/08_tracking/bug/array_at_returns_nil_for_every_index_2026-08-01.md.
                "at" => {
                    let element_ty = match self.module.types.get(receiver.ty) {
                        Some(HirType::Array { element, .. }) => Some(*element),
                        _ => None,
                    };
                    match element_ty {
                        Some(elem) => Some(self.module.types.register(HirType::Pointer {
                            kind: PointerKind::Shared,
                            capability: ReferenceCapability::Shared,
                            inner: elem,
                        })),
                        None => Some(TypeId::ANY),
                    }
                }
                "first" | "last" | "get" | "max" | "min" => {
                    // Returns element type (or Option<element>)
                    if let Some(HirType::Array { element, .. }) = self.module.types.get(receiver.ty) {
                        Some(*element)
                    } else {
                        Some(TypeId::ANY)
                    }
                }
                // JIT method-dispatch audit batch 2 (jit_method_dispatch_audit_2026-07-29,
                // lane DISPATCH2). `copy`/`clone`/`unique`/`sorted`/`reversed`
                // all return a NEW array of the same element type as the
                // receiver — same shape as `take`/`skip`/`drop`/`insert`
                // above (see the MIR expansion in lowering_expr_method.rs).
                "copy" | "clone" | "unique" | "sorted" | "reversed" => Some(receiver.ty),
                // `sort_desc` (lane BATCH3) is the interpreter's non-mutating
                // "return a NEW descending-sorted array" sibling — same
                // shape as `sorted`/`reversed` just above. The MIR lowering
                // (lowering_expr_method.rs) composes `rt_array_sorted` +
                // `rt_array_reversed` rather than calling
                // `rt_array_sort_desc` directly, because that runtime symbol
                // mutates its argument in place (see the comment there).
                "sort_desc" => Some(receiver.ty),
                // `zip(other)` (lane BATCH3) returns an array of
                // `(a, b)` tuples — no single statically-resolvable element
                // type (the two arrays may have different element types),
                // so this falls back to ANY like the `flatten`/dict
                // `"items" | "entries"` entries below.
                "zip" => Some(TypeId::ANY),
                // `flatten` (one level of Array<Array<T>> -> Array<T>) has no
                // statically-resolvable element type in general (nested
                // arrays are frequently ANY-typed) — same ANY fallback the
                // dict `"items" | "entries"` entry below uses.
                "flatten" => Some(TypeId::ANY),
                // `all_truthy`/`any_truthy` (interpreter_method/collections.rs)
                // check truthiness with no predicate lambda and return a raw
                // i64 0/1 from `rt_array_all_truthy`/`rt_array_any_truthy` —
                // same "raw i64 needs generic boxing at print/use" gap class
                // as `index_of` above, typed BOOL instead of I64.
                "all_truthy" | "any_truthy" => Some(TypeId::BOOL),
                // `count_of(needle)` (interpreter_method/collections.rs)
                // counts elements equal to `needle`, a raw i64 from
                // `rt_array_count` — same raw-i64 gap class as `index_of`.
                "count_of" => Some(TypeId::I64),
                _ => None,
            };

            if let Some(ty) = result_ty {
                return Ok(Some(HirExpr {
                    kind: HirExprKind::MethodCall {
                        receiver: Box::new(receiver.clone()),
                        method: method.to_string(),
                        args: hir_args,
                        dispatch: DispatchMode::Static,
                    },
                    ty,
                }));
            }
        }

        // Dict<K, V> methods — thread the key/value types through element
        // reads so field access on the retrieved value resolves against the
        // real struct layout instead of the global most-fields-wins ANY
        // resolver (task #104). Copy out K/V (TypeId is Copy) so the
        // immutable borrow is released before any `register` call below.
        let dict_kv: Option<(TypeId, TypeId)> = match self.module.types.get(receiver.ty) {
            Some(HirType::Dict { key, value }) => Some((*key, *value)),
            _ => None,
        };

        // Any type (Dict, generic containers) methods
        // These are dynamically typed at runtime
        let is_any = matches!(receiver.ty, TypeId::ANY)
            || matches!(self.module.types.get(receiver.ty), Some(HirType::Any))
            || dict_kv.is_some();

        if is_any {
            let result_ty = match method {
                // Dict/Map operations. For a typed Dict<K,V>, `get`/`remove`
                // return the bare value V (the erased builtin dict returns the
                // bare stored word — NOT an Option; see the bug doc iteration
                // 12). `keys`/`values` return typed arrays.
                // `get_or` returns the bare value V (or the caller-supplied
                // default, itself V-typed) — same shape as `get`/`remove`.
                // Without this arm the whole `.get_or(...)` expr fell through
                // to the untyped-ANY default below while the MIR lowering
                // (lowering_expr_method.rs, task: dict_get_or_jit_not_found)
                // produces an UNBOXED V-typed result, so `val r =
                // d.get_or(...)` treated the raw native int as a tagged
                // RuntimeValue and misdecoded it (nil / <invalid-heap> /
                // garbage float) under the JIT — the exact ANY/unboxed-V
                // mismatch class documented just above for `index_of`.
                "get" | "remove" | "get_or" => Some(dict_kv.map(|(_, v)| v).unwrap_or(TypeId::ANY)),
                "insert" | "set" | "put" | "clear" => Some(TypeId::VOID),
                "contains_key" | "has" | "contains" => Some(TypeId::BOOL),
                // "length" synonym — see the string-methods comment above.
                "len" | "length" | "size" => Some(TypeId::I64),
                "keys" => Some(match dict_kv {
                    Some((k, _)) => self.module.types.register(HirType::Array { element: k, size: None }),
                    None => TypeId::ANY,
                }),
                "values" => Some(match dict_kv {
                    Some((_, v)) => self.module.types.register(HirType::Array { element: v, size: None }),
                    None => TypeId::ANY,
                }),
                "items" | "entries" => Some(TypeId::ANY), // Returns iterator/list of pairs
                "is_empty" => Some(TypeId::BOOL),
                // Optional operations (for Option/Result types stored as Any)
                "is_some" | "is_none" | "is_ok" | "is_err" => Some(TypeId::BOOL),
                "unwrap" | "unwrap_or" | "expect" => Some(TypeId::ANY),
                "map" | "and_then" | "or_else" => Some(TypeId::ANY),
                // Type conversion
                "to_string" | "to_text" => Some(TypeId::STRING),
                "to_int" | "to_i64" => Some(TypeId::I64),
                "to_float" | "to_f64" => Some(TypeId::F64),
                "parse_f64" | "parse_float" | "parse_f64_safe" => Some(TypeId::ANY),
                "to_bool" => Some(TypeId::BOOL),
                _ => None,
            };

            if let Some(ty) = result_ty {
                return Ok(Some(HirExpr {
                    kind: HirExprKind::MethodCall {
                        receiver: Box::new(receiver.clone()),
                        method: method.to_string(),
                        args: hir_args,
                        dispatch: DispatchMode::Dynamic, // Dynamic dispatch for Any types
                    },
                    ty,
                }));
            }
        }

        Ok(None)
    }

    // ============================================================================
    // Path expressions (Type.method)
    // ============================================================================

    /// Lower a path expression like Type.method
    ///
    /// Provides helpful error messages for common mistakes:
    /// - `ClassName.new()` should be `ClassName()` (Python-style constructor)
    /// - Other static methods are not yet supported in native compilation
    fn lower_path(&mut self, segments: &[String], ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        if segments.len() == 2 {
            let class_name = &segments[0];
            let method_name = &segments[1];

            // Special case: ClassName.new() should be ClassName()
            if method_name == "new" {
                if self.lenient_types {
                    let qualified = format!("{}.{}", class_name, method_name);
                    self.record_lenient_global(&qualified, LenientGlobalKind::ConstructorAsGlobal);
                    return Ok(HirExpr {
                        kind: HirExprKind::Global(qualified),
                        ty: TypeId::ANY,
                    });
                }
                return Err(LowerError::UseConstructorNotNew {
                    class_name: class_name.clone(),
                });
            }

            if self.module.types.lookup(class_name).is_some() {
                if let Some(expr) = self.try_lower_static_member_value_with_sugar(class_name, method_name, ctx)? {
                    return Ok(expr);
                }
            }

            // Static method reference — produce Global("ClassName.method")
            {
                let qualified = format!("{}.{}", class_name, method_name);
                let ty = self.method_return_types.get(&qualified).copied().unwrap_or(TypeId::ANY);
                return Ok(HirExpr {
                    kind: HirExprKind::Global(qualified),
                    ty,
                });
            }
        }

        if self.lenient_types {
            let joined = segments.join(".");
            self.record_lenient_global(&joined, LenientGlobalKind::UnresolvedPath);
            return Ok(HirExpr {
                kind: HirExprKind::Global(joined),
                ty: TypeId::ANY,
            });
        }

        // Generic path expression not supported
        Err(LowerError::Unsupported(format!("Path expression {:?}", segments)))
    }
}
