use simple_parser as ast;

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    /// Helper to lower builtin function calls with consistent handling
    pub(in crate::hir::lower) fn lower_builtin_call(
        &mut self,
        name: &str,
        args: &[ast::Argument],
        ret_ty: TypeId,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let mut args_hir = Vec::new();
        for arg in args {
            args_hir.push(self.lower_expr(&arg.value, ctx)?);
        }
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
