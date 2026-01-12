//! Tensor and grid literal expression lowering
//!
//! This module contains expression lowering logic for:
//! - Grid literals (matrix notation with | delimiters)
//! - Tensor literals (multidimensional arrays)
//! Both lower to torch.tensor() calls for PyTorch integration.

use simple_parser::{self as ast, Expr};

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    /// Lower grid literal to torch.tensor([[...]]) call
    ///
    /// Example:
    /// ```simple
    /// A = grid:
    ///     | 3 | 1 |
    ///     | 1 | 2 |
    /// ```
    /// Becomes: torch.tensor([[3, 1], [1, 2]])
    ///
    /// With device:
    /// ```simple
    /// A = grid device="cuda":
    ///     | 3 | 1 |
    /// ```
    /// Becomes: torch.tensor([[3, 1]], device="cuda")
    pub(super) fn lower_grid_literal(
        &mut self,
        rows: &[Vec<Box<Expr>>],
        device: &Option<String>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Convert each row to an array
        let mut row_arrays = Vec::new();
        for row in rows {
            let mut cell_exprs = Vec::new();
            for cell in row {
                cell_exprs.push(self.lower_expr(cell.as_ref(), ctx)?);
            }

            // Create array type for this row
            let elem_ty = if let Some(first) = cell_exprs.first() {
                first.ty
            } else {
                TypeId::VOID
            };
            let row_ty = self.module.types.register(HirType::Array {
                element: elem_ty,
                size: Some(cell_exprs.len()),
            });

            row_arrays.push(HirExpr {
                kind: HirExprKind::Array(cell_exprs),
                ty: row_ty,
            });
        }

        // Create nested array type (array of arrays)
        let row_ty = if let Some(first) = row_arrays.first() {
            first.ty
        } else {
            TypeId::VOID
        };
        let grid_ty = self.module.types.register(HirType::Array {
            element: row_ty,
            size: Some(row_arrays.len()),
        });

        // Create the nested array expression
        let nested_array = HirExpr {
            kind: HirExprKind::Array(row_arrays),
            ty: grid_ty,
        };

        // Build arguments: [nested_array] or [nested_array, device="..."]
        let mut args = vec![nested_array];

        // Add device parameter if specified
        if let Some(dev) = device {
            // Create device named argument
            // For now, we'll just append it as a regular argument
            // The interpreter will handle the device parameter
            args.push(HirExpr {
                kind: HirExprKind::String(dev.clone()),
                ty: TypeId::STRING,
            });
        }

        // Create call to torch.tensor(...)
        let func_name = "torch.tensor".to_string();
        let func_expr = HirExpr {
            kind: HirExprKind::Global(func_name),
            ty: TypeId::VOID, // Function type, will be resolved at runtime
        };

        Ok(HirExpr {
            kind: HirExprKind::Call {
                func: Box::new(func_expr),
                args,
            },
            ty: TypeId::I64, // PyTorch tensors are represented as handles (i64/u64)
        })
    }

    /// Lower tensor literal to torch.tensor(...) call
    ///
    /// Handles both slice and flat modes:
    ///
    /// Slice mode example:
    /// ```simple
    /// tensor K: Float [d=2, h=3, w=4]
    ///     slice d=0:
    ///         | h\w | 0 | 1 | 2 | 3 |
    ///         | 0   | 1 | 2 | 3 | 4 |
    ///     slice d=1:
    ///         | h\w | 0 | 1 | 2 | 3 |
    ///         | 0   | 5 | 6 | 7 | 8 |
    /// ```
    ///
    /// Flat mode example:
    /// ```simple
    /// tensor K: Float [d=2, h=3, w=4]
    ///     default: 0
    ///     flat:
    ///         | d | h | w | value |
    ///         | 0 | 0 | 0 | 1.0   |
    ///         | 1 | 2 | 3 | 2.0   |
    /// ```
    pub(super) fn lower_tensor_literal(
        &mut self,
        _dtype: &str,
        dims: &[(String, i64)],
        mode: &Box<ast::TensorMode>,
        device: &Option<String>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        use ast::TensorMode;

        match mode.as_ref() {
            TensorMode::Slice(slices) => {
                // Reconstruct N-D tensor from 2D slices
                let tensor_data = self.reconstruct_tensor_from_slices(slices, dims, ctx)?;
                self.create_torch_tensor_call(tensor_data, device, ctx)
            }
            TensorMode::Flat { default, values } => {
                // Create sparse tensor from coordinate list
                let tensor_data = self.create_sparse_tensor(values, default.as_ref(), dims, ctx)?;
                self.create_torch_tensor_call(tensor_data, device, ctx)
            }
        }
    }

    /// Reconstruct N-dimensional tensor from slice blocks
    ///
    /// Recursively builds nested arrays from slice specifications.
    /// For example, a 3D tensor with slices along dimension 0 will
    /// create an array where each element is a 2D array (the slice content).
    pub(super) fn reconstruct_tensor_from_slices(
        &mut self,
        slices: &[ast::TensorSlice],
        _dims: &[(String, i64)],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        use ast::TensorSliceContent;

        let mut slice_arrays = Vec::new();

        for slice in slices {
            let slice_expr = match &slice.content {
                TensorSliceContent::GridRows(rows) => {
                    // Base case: 2D grid rows
                    let mut row_arrays = Vec::new();
                    for row in rows {
                        let mut cell_exprs = Vec::new();
                        for cell in row {
                            cell_exprs.push(self.lower_expr(cell.as_ref(), ctx)?);
                        }

                        let elem_ty = if let Some(first) = cell_exprs.first() {
                            first.ty
                        } else {
                            TypeId::VOID
                        };
                        let row_ty = self.module.types.register(HirType::Array {
                            element: elem_ty,
                            size: Some(cell_exprs.len()),
                        });

                        row_arrays.push(HirExpr {
                            kind: HirExprKind::Array(cell_exprs),
                            ty: row_ty,
                        });
                    }

                    let row_ty = if let Some(first) = row_arrays.first() {
                        first.ty
                    } else {
                        TypeId::VOID
                    };
                    let grid_ty = self.module.types.register(HirType::Array {
                        element: row_ty,
                        size: Some(row_arrays.len()),
                    });

                    HirExpr {
                        kind: HirExprKind::Array(row_arrays),
                        ty: grid_ty,
                    }
                }
                TensorSliceContent::NestedSlices(nested) => {
                    // Recursive case: nested slices for higher dimensions
                    self.reconstruct_tensor_from_slices(nested, _dims, ctx)?
                }
            };

            slice_arrays.push(slice_expr);
        }

        // Create array type for all slices
        let slice_ty = if let Some(first) = slice_arrays.first() {
            first.ty
        } else {
            TypeId::VOID
        };
        let tensor_ty = self.module.types.register(HirType::Array {
            element: slice_ty,
            size: Some(slice_arrays.len()),
        });

        Ok(HirExpr {
            kind: HirExprKind::Array(slice_arrays),
            ty: tensor_ty,
        })
    }

    /// Create sparse tensor from flat coordinate representation
    ///
    /// NOTE: Flat mode tensor syntax is not yet implemented. Users should use
    /// slice mode syntax instead (explicit slices with grid rows).
    ///
    /// Future implementation would:
    /// 1. Create dense array initialized with default value (or 0)
    /// 2. Iterate through coordinate-value pairs and populate array
    /// 3. For large sparse tensors, generate torch.sparse_coo_tensor call
    /// 4. For small/dense tensors, generate standard torch.tensor call
    ///
    /// This optimization would detect sparsity ratio and choose appropriate
    /// representation automatically. See PyTorch sparse tensor documentation
    /// for COO (coordinate) format details.
    pub(super) fn create_sparse_tensor(
        &mut self,
        values: &[Vec<Box<Expr>>],
        default: Option<&Box<Expr>>,
        dims: &[(String, i64)],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Sparse tensor flat mode is not yet implemented
        // Implementation would check sparsity ratio and emit appropriate torch calls

        // Get default value or use 0
        let default_expr = if let Some(def) = default {
            self.lower_expr(def.as_ref(), ctx)?
        } else {
            HirExpr {
                kind: HirExprKind::Integer(0),
                ty: TypeId::I64,
            }
        };

        // Return clear error directing users to working alternative
        Err(LowerError::Unsupported(
            "Sparse tensor (flat mode) not yet fully implemented. Use slice mode for now."
                .to_string(),
        ))
    }

    /// Create a torch.tensor(...) call with optional device parameter
    pub(super) fn create_torch_tensor_call(
        &mut self,
        data: HirExpr,
        device: &Option<String>,
        _ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let mut args = vec![data];

        if let Some(dev) = device {
            args.push(HirExpr {
                kind: HirExprKind::String(dev.clone()),
                ty: TypeId::STRING,
            });
        }

        let func_name = "torch.tensor".to_string();
        let func_expr = HirExpr {
            kind: HirExprKind::Global(func_name),
            ty: TypeId::VOID,
        };

        Ok(HirExpr {
            kind: HirExprKind::Call {
                func: Box::new(func_expr),
                args,
            },
            ty: TypeId::I64, // Tensor handle
        })
    }
}
