use simple_parser as ast;

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    /// Lower a positional argument list to `Vec<HirExpr>`.
    ///
    /// **Drops `arg.name`** — this is intentional. All call sites using this helper
    /// have already inspected `arg.name` upstream to dispatch struct-init vs positional
    /// paths. Inside the lowering loop, names are never read.
    ///
    /// TODO: if named-arg HIR ever lands (e.g., keyword arguments preserved into HirExpr),
    /// call sites that use this helper must switch back to a name-aware loop.
    pub(in crate::hir::lower) fn lower_call_args(
        &mut self,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Vec<HirExpr>> {
        let mut out = Vec::with_capacity(args.len());
        for arg in args {
            out.push(self.lower_expr(&arg.value, ctx)?);
        }
        Ok(out)
    }

    pub(in crate::hir::lower) fn lower_nonescaping_call_args(
        &mut self,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Vec<HirExpr>> {
        let capability_checkpoint = self.capability_env.clone();
        let result = self.lower_call_args(args, ctx);
        self.capability_env = capability_checkpoint;
        result
    }

    /// Helper to lower builtin function calls with consistent handling
    pub(in crate::hir::lower) fn lower_builtin_call(
        &mut self,
        name: &str,
        args: &[ast::Argument],
        ret_ty: TypeId,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let args_hir = self.lower_call_args(args, ctx)?;
        Ok(HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: name.to_string(),
                args: args_hir,
            },
            ty: ret_ty,
        })
    }

    /// Helper to lower optional dimension argument for gpu.* intrinsics
    /// Returns Vec<HirExpr> with 0 or 1 elements (dimension literal)
    pub(in crate::hir::lower) fn lower_gpu_dim_arg(
        &mut self,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Vec<HirExpr>> {
        if args.is_empty() {
            // No argument - return empty vec, MIR lowering will default to dim 0
            return Ok(vec![]);
        }
        if args.len() > 1 {
            return Err(LowerError::Unsupported(
                "gpu.* functions take at most 1 dimension argument".into(),
            ));
        }
        // Lower the single dimension argument
        let dim_expr = self.lower_expr(&args[0].value, ctx)?;
        Ok(vec![dim_expr])
    }

    /// Parse a swizzle pattern like "xyzw", "xxxx", "rgba", "wzyx" into indices.
    /// Returns None if the pattern is invalid or uses out-of-bounds indices for the vector lanes.
    ///
    /// Swizzle mappings:
    /// - Position: x=0, y=1, z=2, w=3
    /// - Color: r=0, g=1, b=2, a=3
    pub(in crate::hir::lower) fn parse_swizzle_pattern(&self, pattern: &str, max_lanes: u32) -> Option<Vec<u32>> {
        // Swizzle must be 1-4 characters
        if pattern.is_empty() || pattern.len() > 4 {
            return None;
        }

        let mut indices = Vec::with_capacity(pattern.len());
        let mut seen_position = false;
        let mut seen_color = false;

        for c in pattern.chars() {
            let idx = match c {
                'x' | 'r' => {
                    if c == 'x' {
                        seen_position = true;
                    } else {
                        seen_color = true;
                    }
                    0
                }
                'y' | 'g' => {
                    if c == 'y' {
                        seen_position = true;
                    } else {
                        seen_color = true;
                    }
                    1
                }
                'z' | 'b' => {
                    if c == 'z' {
                        seen_position = true;
                    } else {
                        seen_color = true;
                    }
                    2
                }
                'w' | 'a' => {
                    if c == 'w' {
                        seen_position = true;
                    } else {
                        seen_color = true;
                    }
                    3
                }
                _ => return None, // Invalid character
            };

            // Check bounds
            if idx >= max_lanes {
                return None;
            }

            indices.push(idx);
        }

        // Disallow mixing position (xyzw) and color (rgba) in the same swizzle
        if seen_position && seen_color {
            return None;
        }

        Some(indices)
    }
}

impl Lowerer {
    /// If `ty` is an optional over a BoxInt-family scalar (`i8..i64`,
    /// `u8..u32`), return the inner scalar TypeId; otherwise `None`.
    ///
    /// `T?` resolves to `HirType::Pointer { kind: PointerKind::Shared, inner }`
    /// (type_resolver.rs `Type::Optional`), and its runtime slot holds a TAGGED
    /// RuntimeValue (`mir/lower/lowering_core.rs::slot_holds_tagged_value`).
    /// Restricted to the BoxInt family deliberately: those payloads are
    /// BoxInt'd on BOTH representations (raw migration form and boxed
    /// `Some(x)` enum payloads — see the `lower_builtin_call_expr` note in
    /// hir/lower/stmt_lowering.rs), so `UnboxInt` is the exact inverse either
    /// way. `u64` (HeapUInt), `f64`/`f32` (raw enum payload bits vs BoxFloat)
    /// and `bool` (`rt_value_bool`) each have asymmetric representations and
    /// stay on the old path.
    pub(in crate::hir::lower) fn optional_boxint_scalar_inner(&self, ty: TypeId) -> Option<TypeId> {
        match self.module.types.get(ty) {
            Some(HirType::Pointer {
                kind: PointerKind::Shared,
                inner,
                ..
            }) if matches!(
                *inner,
                TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32
            ) =>
            {
                Some(*inner)
            }
            _ => None,
        }
    }

    /// Lower an expression that is about to be tested for ABSENCE (`??`,
    /// `if val`, `match Some(..)`), keeping genuinely-optional array accessors
    /// in their tagged `T?` form.
    ///
    /// `[i64].first()/last()/get(i)/min()/max()/pop()/remove(i)` are typed as the
    /// bare element `T` and MIR unboxes the runtime's tagged result. The
    /// unboxed word then reached the runtime nil test, which treats the raw
    /// words 0/3 as nil: a PRESENT element 3 read as absent under the JIT.
    /// Here the accessor is lowered to the runtime call itself, typed
    /// `Pointer<T>` (what a `T?` slot holds), so presence is the runtime's tag
    /// (NIL vs boxed int), never a value comparison.
    /// Bug: doc/08_tracking/bug/coalesce_optional_accessor_sentinel_value_eaten_jit_2026-08-17.md
    pub(in crate::hir::lower) fn lower_optional_subject(
        &mut self,
        expr: &ast::Expr,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let lowered = self.lower_expr(expr, ctx)?;
        Ok(self.optionalize_array_accessor(lowered))
    }

    pub(in crate::hir::lower) fn optionalize_array_accessor(&mut self, lowered: HirExpr) -> HirExpr {
        let HirExprKind::MethodCall {
            receiver,
            method,
            args,
            ..
        } = &lowered.kind
        else {
            return lowered;
        };
        let element = match self.module.types.get(receiver.ty) {
            Some(HirType::Array { element, .. }) => *element,
            _ => return lowered,
        };
        if !matches!(
            element,
            TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32
        ) || lowered.ty != element
        {
            return lowered;
        }
        let (rt_name, arity) = match method.as_str() {
            "first" => ("rt_array_first", 0),
            "last" => ("rt_array_last", 0),
            "pop" => ("rt_array_pop", 0),
            "min" => ("rt_array_min", 0),
            "max" => ("rt_array_max", 0),
            "get" => ("rt_array_get", 1),
            "remove" => ("rt_array_remove", 1),
            _ => return lowered,
        };
        if args.len() != arity || (arity == 1 && args[0].ty != TypeId::I64) {
            return lowered;
        }
        let mut call_args = vec![(**receiver).clone()];
        call_args.extend(args.iter().cloned());
        let optional_ty = self.module.types.register(HirType::Pointer {
            kind: PointerKind::Shared,
            capability: ast::ReferenceCapability::Shared,
            inner: element,
        });
        HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: rt_name.to_string(),
                args: call_args,
            },
            ty: optional_ty,
        }
    }
}
