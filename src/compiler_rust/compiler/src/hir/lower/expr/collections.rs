//! Collection literal expression lowering
//!
//! This module contains expression lowering logic for collection literals:
//! tuples, arrays, vector literals, struct initialization, and slice expressions.

use simple_parser::{Expr, TupleExprField};

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    /// Lower a tuple literal to HIR
    ///
    /// Creates a tuple type from the types of all elements.
    pub(super) fn lower_tuple(&mut self, exprs: &[Expr], ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        let mut hir_exprs = Vec::new();
        let mut types = Vec::new();
        for e in exprs {
            let hir = self.lower_expr(e, ctx)?;
            types.push(hir.ty);
            hir_exprs.push(hir);
        }

        let tuple_ty = self.module.types.register(HirType::Tuple(types));

        Ok(HirExpr {
            kind: HirExprKind::Tuple(hir_exprs),
            ty: tuple_ty,
        })
    }

    /// Lower a labeled tuple literal to HIR.
    ///
    /// Runtime storage stays positional, while the HIR type carries labels so
    /// `r.name` can lower to the corresponding tuple index.
    pub(super) fn lower_labeled_tuple(
        &mut self,
        fields: &[TupleExprField],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let mut hir_exprs = Vec::new();
        let mut hir_fields = Vec::new();
        for field in fields {
            let hir = self.lower_expr(&field.value, ctx)?;
            hir_fields.push((field.label.clone(), hir.ty));
            hir_exprs.push(hir);
        }

        let tuple_ty = self.module.types.register(HirType::LabeledTuple(hir_fields));

        Ok(HirExpr {
            kind: HirExprKind::Tuple(hir_exprs),
            ty: tuple_ty,
        })
    }

    /// Lower an array literal to HIR
    ///
    /// Creates an array type with a fixed size.
    /// Empty arrays use the configured default element type from type_inference_config.
    pub(super) fn lower_array(&mut self, exprs: &[Expr], ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        let mut hir_exprs = Vec::new();
        for e in exprs {
            hir_exprs.push(self.lower_expr(e, ctx)?);
        }

        let elem_ty = if let Some(first) = hir_exprs.first() {
            match &first.kind {
                HirExprKind::Lambda { params, body, .. } => {
                    let param_types = params.iter().map(|(_, ty)| *ty).collect();
                    self.module.types.register(HirType::Function {
                        params: param_types,
                        ret: body.ty,
                    })
                }
                _ => first.ty,
            }
        } else {
            // Empty array - use configured default or error if strict mode
            if self.type_inference_config.strict_empty_collections {
                return Err(LowerError::EmptyArrayNeedsType);
            }
            self.type_inference_config.empty_array_default
        };

        let arr_ty = self.module.types.register(HirType::Array {
            element: elem_ty,
            size: Some(exprs.len()),
        });

        Ok(HirExpr {
            kind: HirExprKind::Array(hir_exprs),
            ty: arr_ty,
        })
    }

    /// Lower an array repeat expression to HIR: [value; count]
    ///
    /// Creates an array by repeating a value `count` times.
    /// The count must be a compile-time constant for static size inference.
    pub(super) fn lower_array_repeat(
        &mut self,
        value: &Expr,
        count: &Expr,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Infer element type from the value
        let elem_ty = self.infer_type(value, ctx)?;
        let hir_value = self.lower_expr(value, ctx)?;

        // Try to evaluate count as a compile-time constant
        let size = match count {
            Expr::Integer(n) => Some(*n as usize),
            _ => None, // Dynamic size - will be runtime evaluated
        };

        let arr_ty = self.module.types.register(HirType::Array { element: elem_ty, size });

        // Generate array elements by repeating the value
        // For compile-time known sizes, expand to explicit array
        if let Some(n) = size {
            let hir_exprs: Vec<_> = std::iter::repeat_n(hir_value, n).collect();
            Ok(HirExpr {
                kind: HirExprKind::Array(hir_exprs),
                ty: arr_ty,
            })
        } else {
            // For dynamic sizes, lower count and use ArrayRepeat HIR node
            let hir_count = self.lower_expr(count, ctx)?;
            Ok(HirExpr {
                kind: HirExprKind::ArrayRepeat {
                    value: Box::new(hir_value),
                    count: Box::new(hir_count),
                },
                ty: arr_ty,
            })
        }
    }

    /// Lower a vector literal to HIR
    ///
    /// Creates a SIMD vector type with the number of lanes equal to the number of elements.
    /// Empty vectors use the configured default element type from type_inference_config.
    pub(super) fn lower_vec_literal(&mut self, exprs: &[Expr], ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        let mut hir_exprs = Vec::new();
        let elem_ty = if let Some(first) = exprs.first() {
            self.infer_type(first, ctx)?
        } else {
            // Empty vector - use configured default or error if strict mode
            if self.type_inference_config.strict_empty_collections {
                return Err(LowerError::EmptyArrayNeedsType);
            }
            self.type_inference_config.empty_vector_default
        };

        for e in exprs {
            hir_exprs.push(self.lower_expr(e, ctx)?);
        }

        let vec_ty = self.module.types.register(HirType::Simd {
            lanes: exprs.len() as u32,
            element: elem_ty,
        });

        Ok(HirExpr {
            kind: HirExprKind::VecLiteral(hir_exprs),
            ty: vec_ty,
        })
    }

    /// Lower a struct initialization expression to HIR
    ///
    /// Creates a struct instance with field initializers.
    /// Supports "Self" keyword to refer to the current class/struct type.
    pub(super) fn lower_struct_init(
        &mut self,
        name: &str,
        fields: &[(String, Expr)],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        use crate::hir::lower::error::LowerError;

        // Resolve struct type (handle "Self" keyword)
        let struct_ty = if name == "Self" {
            if let Some(class_ty) = self.current_class_type {
                class_ty
            } else {
                return Err(LowerError::UnknownType {
                    type_name: "Self".to_string(),
                    available_types: vec![],
                });
            }
        } else {
            match self.module.types.lookup(name) {
                Some(ty) => ty,
                None if self.lenient_types => TypeId::ANY,
                None => {
                    return Err(LowerError::UnknownType {
                        type_name: name.to_string(),
                        available_types: self.module.types.all_type_names(),
                    });
                }
            }
        };

        // ROOT FIX (bug simpleos_native_build_field_defaults_and_boxed_trait_dispatch,
        // 2026-07-16): see `lower_struct_init_fields` doc comment below for the
        // full root-cause writeup. Brace-literal form (`S { field: v }`) always
        // gives every field a name, so route it through the same
        // declared-order-with-nil-fill resolver as the paren-call constructor
        // form (`S(field: v)`, hir/lower/expr/calls.rs) uses.
        let provided: Vec<(Option<&str>, &Expr)> = fields.iter().map(|(n, e)| (Some(n.as_str()), e)).collect();
        let fields_hir = self.lower_struct_init_fields(name, struct_ty, &provided, ctx)?;

        Ok(HirExpr {
            kind: HirExprKind::StructInit {
                ty: struct_ty,
                fields: fields_hir,
            },
            ty: struct_ty,
        })
    }

    /// Build the declared-order field HIR list for a struct/class
    /// construction (either AST shape: brace literal `S { field: v }` or
    /// paren-call constructor `S(field: v)`).
    ///
    /// ROOT FIX (bug simpleos_native_build_field_defaults_and_boxed_trait_dispatch,
    /// 2026-07-16): MIR's StructInit lowering (`lower_struct_init_expr` in
    /// mir/lower/lowering_expr_struct.rs) always derives
    /// `field_offsets`/`field_types` from the struct's FULL declared field
    /// list, in DECLARED order, via the type registry -- regardless of how
    /// many fields the construction site actually wrote out. Both HIR
    /// construction sites previously lowered exactly the arguments given, in
    /// the ORDER WRITTEN IN SOURCE (the paren-call site went further and
    /// dropped argument names entirely via `lower_call_args`, "lower
    /// arguments as positional field initializers"), with no regard for the
    /// field's declared name/index and no fill-in for omitted `= default`
    /// fields. Any call that (a) omits a field with a declared default
    /// (relying on the class-level default, e.g.
    /// `vulkan_backend: VulkanBackend? = nil`) or (b) writes fields out of
    /// declared order, silently shifted every later field's value into its
    /// neighbor's byte slot; omitted trailing fields were left holding
    /// whatever was already on the heap (poison), not the declared default.
    ///
    /// Resolve the struct's true declared field order -- locally via the type
    /// registry, falling back to the cross-module `global_struct_defs` map
    /// for closure-discovered types whose local TypeId erased to ANY (the
    /// same fallback `access.rs` already uses for field READS) -- and build
    /// the field list in THAT order: a named argument goes to its matching
    /// declared slot, a positional (unnamed) argument fills the next
    /// not-yet-assigned slot in declared order (preserving plain positional
    /// construction), and any declared slot nothing fills gets a `nil`
    /// placeholder instead of being left unset.
    pub(super) fn lower_struct_init_fields(
        &mut self,
        name: &str,
        struct_ty: TypeId,
        provided: &[(Option<&str>, &Expr)],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Vec<HirExpr>> {
        // `from_registry` records whether `declared` came from the LOCAL type
        // registry (authoritative for this struct) or from the cross-module
        // `global_struct_defs` BARE-NAME fallback. The fallback keys on the
        // unqualified name, so two same-named structs in different modules
        // collide and it can hand back the wrong field list -- fine as a
        // best-effort ORDERING hint (its prior use), but not sound enough to
        // reject a name on. Only the registry list gates the hard error below.
        let mut from_registry = true;
        let declared_field_names: Option<Vec<String>> = self
            .module
            .types
            .get(struct_ty)
            .and_then(|hir_ty| match hir_ty {
                HirType::Struct { fields: sf, .. } => Some(sf.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>()),
                _ => None,
            })
            .or_else(|| {
                from_registry = false;
                let bare_name = name.rsplit('.').next().unwrap_or(name);
                self.global_struct_defs.as_ref().and_then(|defs| {
                    defs.get(bare_name)
                        .map(|fs| fs.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>())
                })
            });

        let Some(declared) = declared_field_names else {
            // Struct declaration not found anywhere (fully erased, no
            // registry entry) -- fall back to lowering exactly what was
            // written, in source order, matching prior behavior for this
            // unresolvable case.
            let mut out = Vec::with_capacity(provided.len());
            for (_, expr) in provided {
                out.push(self.lower_expr(expr, ctx)?);
            }
            return Ok(out);
        };

        // Same-bare-name variant selection: the local registry is
        // last-registration-wins, so `declared` may be a DIFFERENT module's
        // layout for this name. Only when that layout does NOT cover every
        // provided named argument — i.e. the construction would hit the
        // hard-error gate below — and exactly ONE recorded variant covers them
        // all, adopt that variant's layout. When the registry layout already
        // covers everything, keep it: swapping layouts for a covering
        // constructor risks writer/reader divergence, which is worse than the
        // de-JIT this avoids. Ambiguous coverage keeps the registry layout.
        let mut declared = declared;
        let bare_name = name.rsplit('.').next().unwrap_or(name);
        let provided_names: Vec<&str> = provided.iter().filter_map(|(n, _)| *n).collect();
        let registry_covers = provided_names.iter().all(|pn| declared.iter().any(|d| d == pn));
        if !registry_covers && !provided_names.is_empty() {
            if let Some(variants) = self
                .duplicate_global_struct_defs
                .as_ref()
                .and_then(|defs| defs.get(bare_name))
            {
                if variants.len() > 1 {
                    let mut covering = variants.iter().filter(|fields| {
                        provided_names
                            .iter()
                            .all(|pn| fields.iter().any(|(fname, _)| fname == pn))
                    });
                    let first = covering.next();
                    let second = covering.next();
                    if let (Some(best), None) = (first, second) {
                        declared = best.iter().map(|(n, _)| n.clone()).collect();
                    }
                }
            }
        }

        // ROOT FIX (bug jit_named_ctor_accepts_unknown_field_name, 2026-08-08):
        // reject a named argument whose name matches NO declared field.
        //
        // Before this check, an unknown name was inserted into `named` below,
        // never consumed by the declared-order loop (which only ever looks up
        // names it already knows), and never reported. The declared slot the
        // author meant to fill therefore stayed unfilled and fell through to
        // the `HirExprKind::Nil` placeholder at the bottom of that loop --
        // which MIR lowers to `ConstInt { value: 3 }`, the runtime NIL tag
        // (`TAG_SPECIAL=0b011 | SPECIAL_NIL=0`, see
        // mir/lower/lowering_expr_literal.rs `lower_nil_expr`). Read back
        // through an `i64`-typed field, that tag surfaces untagged as the
        // literal integer `3`. So ONE mistyped field name silently corrupted a
        // DIFFERENT, correctly-spelled field with a leaked discriminant, with
        // no diagnostic on any line: `class Font { id: i64, size: i64 }`
        // constructed as `Font(bogus: 111, size: 8)` printed `id=3 size=8`,
        // and `Font(id: 5, bogus: 999)` printed `size=3`.
        //
        // The `3` is NOT, as an earlier characterisation of this bug guessed,
        // the preceding argument's value -- a three-field class proves it:
        // `T3(b: 7, zzz: 99)` printed `a=3 b=7 c=3`, two independent slots
        // both holding the same tag.
        //
        // The interpreter already rejected this correctly
        // (interpreter_call/core/class_instantiation.rs, "class `X` has no
        // field named `Y`"); only the compiled/JIT path accepted it, and
        // `bin/simple run` is the JIT while `bin/simple test` is the
        // interpreter -- so the divergence was invisible to the test suite.
        //
        // Deliberately NOT gated on the bare-name fallback list (see
        // `from_registry` above), and NOT applied on the fully-erased/lenient
        // branch below, both of which can carry a field list that is merely a
        // guess.
        // SOUNDNESS GATE. Rejecting on `declared` alone false-positives at ~5%
        // of repo files (21/400 in a sweep on 2026-08-08: `Rect` field `x`,
        // `Span` field `end`, `Diagnostic` field `range` -- all obviously REAL
        // fields). Cause: this repo has many same-bare-named structs (7 `Rect`,
        // 7 `Span`), and the local registry can resolve `struct_ty` to a
        // DIFFERENT module's struct of that name than the call site meant. So
        // "not in `declared`" does NOT prove "typo"; it may only prove the
        // registry picked the wrong layout (a separate, pre-existing
        // resolution defect that this check must not be the messenger for).
        //
        // Only report a name that matches NO candidate layout carrying that
        // bare type name -- the local registry list UNION every cross-module
        // layout the driver recorded for the name. A genuine typo (`bogus`,
        // `zzz`) is in none of them; a collision victim is in at least one.
        // Only a struct DECLARED IN THIS SAME FILE is safe to reject against.
        // ~1,522 class/struct bare names are duplicated across src/{compiler,lib,app},
        // and `TypeRegistry::name_to_id` is bare-keyed and last-registration-wins,
        // so for an IMPORTED name `struct_ty` may resolve to a different module's
        // struct than the call site meant -- "not in `declared`" would then mean
        // only "the registry picked the wrong layout", a separate defect (the
        // `struct_field_order` collision family, fixed for MIR field READS in
        // b9e23914a0e). Measured on 2026-08-08: rejecting on `declared` alone fired
        // on 21 of 400 repo files, and every one inspected was a collision, not a
        // typo -- the same sweep reported BOTH `Span` field `end` AND `Span` field
        // `end_pos`, which is only possible with two different `Span` structs
        // (00.common/diagnostics/span.spl has `end`, 10.frontend/core/lexer_types.spl
        // has `end_pos`). Neither cross-module map above can rescue those: both are
        // populated only by the native_project driver and are None under
        // `simple run`, and the losing declaration is absent from the registry
        // entirely, so the collision is simply not observable from HIR here.
        //
        // Same-file declarations have no such ambiguity: the entry validated
        // against is provably the one the author wrote. That covers the reported
        // defect and rejects genuine typos with zero false positives (0 of 400 on
        // the same sweep). The imported-struct case stays permissive and is called
        // out as the remaining gap in the bug doc.
        let declared_here = from_registry
            && self
                .struct_decl_files
                .get(name.rsplit('.').next().unwrap_or(name))
                .is_some_and(|decl_file| *decl_file == self.current_file);
        if declared_here {
            for (opt_name, _) in provided {
                if let Some(n) = opt_name {
                    if !declared.iter().any(|d| d == n) {
                        return Err(crate::hir::lower::error::LowerError::CannotInferFieldType {
                            struct_name: name.to_string(),
                            field: (*n).to_string(),
                            available_fields: declared.clone(),
                        });
                    }
                }
            }
        }

        let mut named: std::collections::HashMap<&str, &Expr> = std::collections::HashMap::new();
        let mut positional: Vec<&Expr> = Vec::new();
        for (opt_name, expr) in provided {
            match opt_name {
                Some(n) => {
                    named.insert(n, expr);
                }
                None => positional.push(expr),
            }
        }

        let mut pos_iter = positional.into_iter();
        let mut out = Vec::with_capacity(declared.len());
        for field_name in &declared {
            // Cloned OUT of `self` first: an `if let` on a borrow of
            // `self.struct_field_defaults` would keep that borrow alive across
            // the `self.lower_expr(&mut self, ..)` call in its body.
            let declared_default: Option<Expr> = self
                .struct_field_defaults
                .get(bare_name)
                .and_then(|m| m.get(field_name.as_str()))
                .cloned();
            if let Some(expr) = named.get(field_name.as_str()) {
                out.push(self.lower_expr(expr, ctx)?);
            } else if let Some(expr) = pos_iter.next() {
                out.push(self.lower_expr(expr, ctx)?);
            } else if let Some(default_expr) = declared_default {
                // ROOT FIX (JIT omitted-field-default, 2026-08-17): a declared
                // `= default` fills its own slot. Previously EVERY unwritten
                // slot got the `Nil` placeholder below, which MIR lowers to the
                // raw nil tag `3`; read back through an `i64` field that
                // surfaced as the literal `3`, so `D()` on
                // `class D: var n: i64 = 0; var m: i64 = 7` printed `n=3 m=3`
                // under the JIT against `n=0 m=7` in the interpreter.
                // A field with NO declared default still gets `Nil`, unchanged.
                out.push(self.lower_expr(&default_expr, ctx)?);
            } else {
                out.push(HirExpr {
                    kind: HirExprKind::Nil,
                    ty: TypeId::NIL,
                });
            }
        }
        Ok(out)
    }

    /// Lower a dictionary literal to HIR: {key: value, ...}
    ///
    /// Creates a dictionary with key-value pairs. A HOMOGENEOUS literal gets a
    /// concrete `Dict { key, value }` type inferred from its entries, exactly
    /// as `lower_array` infers `Array { element }`; a heterogeneous, empty, or
    /// otherwise unresolvable literal stays `TypeId::ANY` (dictionaries are
    /// dynamically typed at runtime, and every dynamic-dict consumer keeps its
    /// current behaviour).
    ///
    /// Why the inference is load-bearing, not a nicety: `d[k]` lowers via
    /// `lower_index_expr`, which recovers the element type from
    /// `HirType::Dict { value, .. }` and only then pairs `rt_index_get` with the
    /// `UnboxInt` that turns the returned RuntimeValue back into a native int.
    /// With `ty: ANY` the receiver is not a Dict in the registry, the recovery
    /// yields ANY, NO `UnboxInt` is emitted, and the raw RuntimeValue leaks into
    /// an i64-typed VReg — `val d = {1: 10, 2: 20}; d[2]` printed
    /// `<value:0x14>` under the Cranelift JIT while the annotated
    /// `val d: {i64: i64} = ...` printed `20`, and the interpreter (which is
    /// tag-aware end to end) printed `20` for both. The same erasure left the
    /// method path dispatching on the unqualified name `get` instead of
    /// `Dict.get`, so `d.get(k)` diverged from the annotated form too.
    pub(super) fn lower_dict(&mut self, pairs: &[(Expr, Expr)], ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        let mut hir_pairs = Vec::new();

        for (key, value) in pairs {
            let key_hir = self.lower_expr(key, ctx)?;
            let value_hir = self.lower_expr(value, ctx)?;
            hir_pairs.push((key_hir, value_hir));
        }

        let dict_ty = self.infer_dict_literal_type(&hir_pairs);

        Ok(HirExpr {
            kind: HirExprKind::Dict(hir_pairs),
            ty: dict_ty,
        })
    }

    /// Infer `Dict { key, value }` for a homogeneous dict literal, or `ANY`.
    ///
    /// Deliberately conservative — it only commits to a concrete Dict type when
    /// the literal leaves no room for doubt:
    /// - non-empty (`{}` has nothing to infer from and stays ANY, as before),
    /// - every key shares one TypeId and every value shares one TypeId,
    /// - neither of those TypeIds is itself ANY/NIL (an erased entry type would
    ///   register a `Dict { .., value: ANY }` that reads back exactly like ANY
    ///   for unboxing purposes while still flipping method dispatch onto the
    ///   `Dict.*` qualified names — behaviour change with no correctness win),
    /// - no lambda-kind entry, whose `HirExpr::ty` is not the function type
    ///   (`lower_array` reconstructs it specially; a dict of closures has no
    ///   unboxing stake, so it simply stays ANY here).
    ///
    /// Any literal failing these falls through to `TypeId::ANY`, i.e. exactly
    /// the behaviour every dict had before this inference existed.
    fn infer_dict_literal_type(&mut self, hir_pairs: &[(HirExpr, HirExpr)]) -> TypeId {
        let Some((first_key, first_value)) = hir_pairs.first() else {
            return TypeId::ANY;
        };
        let key_ty = first_key.ty;
        let value_ty = first_value.ty;
        if matches!(key_ty, TypeId::ANY | TypeId::NIL) || matches!(value_ty, TypeId::ANY | TypeId::NIL) {
            return TypeId::ANY;
        }
        let uniform = hir_pairs.iter().all(|(k, v)| {
            k.ty == key_ty
                && v.ty == value_ty
                && !matches!(k.kind, HirExprKind::Lambda { .. })
                && !matches!(v.kind, HirExprKind::Lambda { .. })
        });
        if !uniform {
            return TypeId::ANY;
        }
        self.module.types.register(HirType::Dict {
            key: key_ty,
            value: value_ty,
        })
    }

    /// Lower a slice expression to HIR: receiver[start:end:step]
    ///
    /// Converts to a call to rt_slice(collection, start, end, step).
    /// Handles defaults:
    /// - start: 0 if None
    /// - end: collection.len() if None (uses a large value as sentinel)
    /// - step: 1 if None
    pub(super) fn lower_slice(
        &mut self,
        receiver: &Expr,
        start: Option<&Expr>,
        end: Option<&Expr>,
        step: Option<&Expr>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Lower the receiver (the collection being sliced)
        let receiver_hir = self.lower_expr(receiver, ctx)?;
        let receiver_ty = receiver_hir.ty;

        // Determine result type (same as input for arrays/strings)
        let result_ty = receiver_ty;

        // Lower start (default: 0)
        let start_hir = if let Some(s) = start {
            self.lower_expr(s, ctx)?
        } else {
            HirExpr {
                kind: HirExprKind::Integer(0),
                ty: TypeId::I64,
            }
        };

        // Lower end (default: large sentinel value, runtime will clamp to len)
        // We use i64::MAX as a sentinel for "to the end"
        let end_hir = if let Some(e) = end {
            self.lower_expr(e, ctx)?
        } else {
            HirExpr {
                kind: HirExprKind::Integer(i64::MAX),
                ty: TypeId::I64,
            }
        };

        // Lower step (default: 1)
        let step_hir = if let Some(s) = step {
            self.lower_expr(s, ctx)?
        } else {
            HirExpr {
                kind: HirExprKind::Integer(1),
                ty: TypeId::I64,
            }
        };

        self.require_integer_index_operand(receiver_ty, start_hir.ty)?;
        self.require_integer_index_operand(receiver_ty, end_hir.ty)?;
        self.require_integer_index_operand(receiver_ty, step_hir.ty)?;

        // Generate a builtin call to rt_slice
        Ok(HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: "rt_slice".to_string(),
                args: vec![receiver_hir, start_hir, end_hir, step_hir],
            },
            ty: result_ty,
        })
    }
}
