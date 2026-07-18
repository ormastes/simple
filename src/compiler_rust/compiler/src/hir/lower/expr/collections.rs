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
        let declared_field_names: Option<Vec<String>> = self
            .module
            .types
            .get(struct_ty)
            .and_then(|hir_ty| match hir_ty {
                HirType::Struct { fields: sf, .. } => Some(sf.iter().map(|(n, _)| n.clone()).collect::<Vec<_>>()),
                _ => None,
            })
            .or_else(|| {
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
            if let Some(expr) = named.get(field_name.as_str()) {
                out.push(self.lower_expr(expr, ctx)?);
            } else if let Some(expr) = pos_iter.next() {
                out.push(self.lower_expr(expr, ctx)?);
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
    /// Creates a dictionary with key-value pairs.
    /// The type is represented as ANY since dictionaries are dynamically typed at runtime.
    pub(super) fn lower_dict(&mut self, pairs: &[(Expr, Expr)], ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        let mut hir_pairs = Vec::new();

        for (key, value) in pairs {
            let key_hir = self.lower_expr(key, ctx)?;
            let value_hir = self.lower_expr(value, ctx)?;
            hir_pairs.push((key_hir, value_hir));
        }

        Ok(HirExpr {
            kind: HirExprKind::Dict(hir_pairs),
            ty: TypeId::ANY, // Dictionaries are dynamically typed
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
