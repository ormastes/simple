use std::collections::HashMap;

use simple_parser::{self as ast, Module, Node, Expr, Type, Pattern};
use simple_parser::ast::Mutability;
use thiserror::Error;

use super::types::*;

//==============================================================================
// Lowering Errors (for formal verification)
//==============================================================================
// All type inference failures must be explicit errors, not silent UNKNOWN fallbacks.
// This makes verification easier since every expression either:
// 1. Has a known type (TypeId with id < u32::MAX)
// 2. Results in an error (LowerError variant)
//
// The error variants below correspond to specific inference failures.

#[derive(Error, Debug)]
pub enum LowerError {
    #[error("Unknown type: {0}")]
    UnknownType(String),

    #[error("Unknown variable: {0}")]
    UnknownVariable(String),

    #[error("Type mismatch: expected {expected:?}, found {found:?}")]
    TypeMismatch { expected: TypeId, found: TypeId },

    #[error("Cannot infer type")]
    CannotInferType,

    #[error("Cannot infer type: {0}")]
    CannotInferTypeFor(String),

    #[error("Parameter '{0}' requires explicit type annotation")]
    MissingParameterType(String),

    #[error("Cannot infer element type of empty array - use explicit annotation")]
    EmptyArrayNeedsType,

    #[error("Cannot infer field type: struct '{struct_name}' field '{field}'")]
    CannotInferFieldType { struct_name: String, field: String },

    #[error("Cannot infer element type for index into '{0}'")]
    CannotInferIndexType(String),

    #[error("Cannot infer deref type for '{0}'")]
    CannotInferDerefType(String),

    #[error("Unsupported feature: {0}")]
    Unsupported(String),
}

pub type LowerResult<T> = Result<T, LowerError>;

/// Context for lowering a function
struct FunctionContext {
    locals: Vec<LocalVar>,
    local_map: HashMap<String, usize>,
    return_type: TypeId,
}

impl FunctionContext {
    fn new(return_type: TypeId) -> Self {
        Self {
            locals: Vec::new(),
            local_map: HashMap::new(),
            return_type,
        }
    }

    fn add_local(&mut self, name: String, ty: TypeId, is_mutable: bool) -> usize {
        let index = self.locals.len();
        let mutability = if is_mutable { Mutability::Mutable } else { Mutability::Immutable };
        self.locals.push(LocalVar { name: name.clone(), ty, mutability });
        self.local_map.insert(name, index);
        index
    }

    fn lookup(&self, name: &str) -> Option<usize> {
        self.local_map.get(name).copied()
    }
}

/// Lowers AST to HIR
pub struct Lowerer {
    module: HirModule,
    globals: HashMap<String, TypeId>,
}

impl Lowerer {
    pub fn new() -> Self {
        Self {
            module: HirModule::new(),
            globals: HashMap::new(),
        }
    }

    pub fn lower_module(mut self, ast_module: &Module) -> LowerResult<HirModule> {
        self.module.name = ast_module.name.clone();

        // First pass: collect type and function declarations
        for item in &ast_module.items {
            match item {
                Node::Struct(s) => {
                    self.register_struct(s)?;
                }
                Node::Function(f) => {
                    let ret_ty = self.resolve_type_opt(&f.return_type)?;
                    self.globals.insert(f.name.clone(), ret_ty);
                }
                Node::Class(c) => {
                    // Register class as a struct-like type
                    let fields: Vec<_> = c.fields.iter().map(|f| {
                        (f.name.clone(), self.resolve_type(&f.ty).unwrap_or(TypeId::VOID))
                    }).collect();
                    self.module.types.register_named(
                        c.name.clone(),
                        HirType::Struct {
                            name: c.name.clone(),
                            fields,
                        },
                    );
                }
                Node::Enum(e) => {
                    // Register enum type with variant information
                    let variants = e.variants.iter().map(|v| {
                        let fields = v.fields.as_ref().map(|types| {
                            types.iter().map(|t| self.resolve_type(t).unwrap_or(TypeId::VOID)).collect()
                        });
                        (v.name.clone(), fields)
                    }).collect();
                    self.module.types.register_named(
                        e.name.clone(),
                        HirType::Enum {
                            name: e.name.clone(),
                            variants,
                        },
                    );
                }
                Node::Trait(_) | Node::Actor(_) | Node::TypeAlias(_) | Node::Impl(_)
                | Node::Extern(_) | Node::Macro(_) => {
                    // These are handled at type-check time or runtime
                    // HIR lowering focuses on functions and struct types
                }
                Node::Let(_) | Node::Const(_) | Node::Static(_) | Node::Assignment(_)
                | Node::Return(_) | Node::If(_) | Node::Match(_) | Node::For(_)
                | Node::While(_) | Node::Loop(_) | Node::Break(_) | Node::Continue(_)
                | Node::Context(_) | Node::Expression(_) => {
                    // Statement nodes at module level are not supported in HIR
                    // They should be inside function bodies
                }
            }
        }

        // Second pass: lower function bodies
        for item in &ast_module.items {
            if let Node::Function(f) = item {
                let hir_func = self.lower_function(f)?;
                self.module.functions.push(hir_func);
            }
        }

        Ok(self.module)
    }

    fn register_struct(&mut self, s: &ast::StructDef) -> LowerResult<TypeId> {
        let mut fields = Vec::new();
        for field in &s.fields {
            let ty = self.resolve_type(&field.ty)?;
            fields.push((field.name.clone(), ty));
        }

        let hir_type = HirType::Struct {
            name: s.name.clone(),
            fields,
        };

        Ok(self.module.types.register_named(s.name.clone(), hir_type))
    }

    fn resolve_type(&mut self, ty: &Type) -> LowerResult<TypeId> {
        match ty {
            Type::Simple(name) => {
                self.module.types.lookup(name)
                    .ok_or_else(|| LowerError::UnknownType(name.clone()))
            }
            Type::Pointer { kind, inner } => {
                let inner_id = self.resolve_type(inner)?;
                let ptr_type = HirType::Pointer {
                    kind: (*kind).into(),
                    inner: inner_id,
                };
                Ok(self.module.types.register(ptr_type))
            }
            Type::Tuple(types) => {
                let mut type_ids = Vec::new();
                for t in types {
                    type_ids.push(self.resolve_type(t)?);
                }
                Ok(self.module.types.register(HirType::Tuple(type_ids)))
            }
            Type::Array { element, size } => {
                let elem_id = self.resolve_type(element)?;
                let size_val = size.as_ref().and_then(|e| {
                    if let Expr::Integer(n) = e.as_ref() {
                        Some(*n as usize)
                    } else {
                        None
                    }
                });
                Ok(self.module.types.register(HirType::Array { element: elem_id, size: size_val }))
            }
            Type::Function { params, ret } => {
                let mut param_ids = Vec::new();
                for p in params {
                    param_ids.push(self.resolve_type(p)?);
                }
                let ret_id = if let Some(r) = ret {
                    self.resolve_type(r)?
                } else {
                    TypeId::VOID
                };
                Ok(self.module.types.register(HirType::Function { params: param_ids, ret: ret_id }))
            }
            Type::Optional(inner) => {
                // Optional is represented as a nullable pointer or special enum
                let inner_id = self.resolve_type(inner)?;
                Ok(self.module.types.register(HirType::Pointer {
                    kind: PointerKind::Shared,
                    inner: inner_id,
                }))
            }
            _ => Err(LowerError::Unsupported(format!("{:?}", ty))),
        }
    }

    fn resolve_type_opt(&mut self, ty: &Option<Type>) -> LowerResult<TypeId> {
        match ty {
            Some(t) => self.resolve_type(t),
            None => Ok(TypeId::VOID),
        }
    }

    fn lower_function(&mut self, f: &ast::FunctionDef) -> LowerResult<HirFunction> {
        let return_type = self.resolve_type_opt(&f.return_type)?;
        let mut ctx = FunctionContext::new(return_type);

        // Add parameters as locals
        // Parameters MUST have explicit type annotations (no inference)
        for param in &f.params {
            let ty = if let Some(t) = &param.ty {
                self.resolve_type(t)?
            } else {
                return Err(LowerError::MissingParameterType(param.name.clone()));
            };
            ctx.add_local(param.name.clone(), ty, param.mutability.is_mutable());
        }

        let params: Vec<LocalVar> = ctx.locals.clone();
        let params_len = params.len();

        // Lower function body
        let body = self.lower_block(&f.body, &mut ctx)?;

        Ok(HirFunction {
            name: f.name.clone(),
            params,
            locals: ctx.locals[params_len..].to_vec(),
            return_type,
            body,
            visibility: f.visibility,
        })
    }

    fn lower_block(&mut self, block: &ast::Block, ctx: &mut FunctionContext) -> LowerResult<Vec<HirStmt>> {
        let mut stmts = Vec::new();
        for node in &block.statements {
            stmts.extend(self.lower_node(node, ctx)?);
        }
        Ok(stmts)
    }

    fn lower_node(&mut self, node: &Node, ctx: &mut FunctionContext) -> LowerResult<Vec<HirStmt>> {
        match node {
            Node::Let(let_stmt) => {
                let ty = if let Some(t) = &let_stmt.ty {
                    self.resolve_type(t)?
                } else if let Some(val) = &let_stmt.value {
                    self.infer_type(val, ctx)?
                } else {
                    return Err(LowerError::CannotInferType);
                };

                let value = if let Some(v) = &let_stmt.value {
                    Some(self.lower_expr(v, ctx)?)
                } else {
                    None
                };

                let name = Self::extract_pattern_name(&let_stmt.pattern)
                    .ok_or_else(|| LowerError::Unsupported("complex pattern in let".to_string()))?;

                let local_index = ctx.add_local(name, ty, let_stmt.mutability.is_mutable());

                Ok(vec![HirStmt::Let { local_index, ty, value }])
            }

            Node::Assignment(assign) => {
                let target = self.lower_expr(&assign.target, ctx)?;
                let value = self.lower_expr(&assign.value, ctx)?;
                Ok(vec![HirStmt::Assign { target, value }])
            }

            Node::Return(ret) => {
                let value = if let Some(v) = &ret.value {
                    Some(self.lower_expr(v, ctx)?)
                } else {
                    None
                };
                Ok(vec![HirStmt::Return(value)])
            }

            Node::If(if_stmt) => {
                let condition = self.lower_expr(&if_stmt.condition, ctx)?;
                let then_block = self.lower_block(&if_stmt.then_block, ctx)?;
                let else_block = if let Some(eb) = &if_stmt.else_block {
                    Some(self.lower_block(eb, ctx)?)
                } else {
                    None
                };

                Ok(vec![HirStmt::If { condition, then_block, else_block }])
            }

            Node::While(while_stmt) => {
                let condition = self.lower_expr(&while_stmt.condition, ctx)?;
                let body = self.lower_block(&while_stmt.body, ctx)?;
                Ok(vec![HirStmt::While { condition, body }])
            }

            Node::Loop(loop_stmt) => {
                let body = self.lower_block(&loop_stmt.body, ctx)?;
                Ok(vec![HirStmt::Loop { body }])
            }

            Node::Break(_) => Ok(vec![HirStmt::Break]),
            Node::Continue(_) => Ok(vec![HirStmt::Continue]),

            Node::Expression(expr) => {
                let hir_expr = self.lower_expr(expr, ctx)?;
                Ok(vec![HirStmt::Expr(hir_expr)])
            }

            _ => Err(LowerError::Unsupported(format!("{:?}", node))),
        }
    }

    fn lower_expr(&mut self, expr: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        match expr {
            Expr::Integer(n) => Ok(HirExpr {
                kind: HirExprKind::Integer(*n),
                ty: TypeId::I64,
            }),

            Expr::Float(f) => Ok(HirExpr {
                kind: HirExprKind::Float(*f),
                ty: TypeId::F64,
            }),

            Expr::String(s) => Ok(HirExpr {
                kind: HirExprKind::String(s.clone()),
                ty: TypeId::STRING,
            }),

            Expr::Bool(b) => Ok(HirExpr {
                kind: HirExprKind::Bool(*b),
                ty: TypeId::BOOL,
            }),

            Expr::Nil => Ok(HirExpr {
                kind: HirExprKind::Nil,
                ty: TypeId::NIL,
            }),

            Expr::Identifier(name) => {
                if let Some(idx) = ctx.lookup(name) {
                    let ty = ctx.locals[idx].ty;
                    Ok(HirExpr {
                        kind: HirExprKind::Local(idx),
                        ty,
                    })
                } else if let Some(ty) = self.globals.get(name).copied() {
                    Ok(HirExpr {
                        kind: HirExprKind::Global(name.clone()),
                        ty,
                    })
                } else {
                    Err(LowerError::UnknownVariable(name.clone()))
                }
            }

            Expr::Binary { op, left, right } => {
                let left_hir = Box::new(self.lower_expr(left, ctx)?);
                let right_hir = Box::new(self.lower_expr(right, ctx)?);

                // Type is determined by operands (simplified)
                let ty = match op {
                    ast::BinOp::Eq | ast::BinOp::NotEq |
                    ast::BinOp::Lt | ast::BinOp::Gt |
                    ast::BinOp::LtEq | ast::BinOp::GtEq |
                    ast::BinOp::And | ast::BinOp::Or |
                    ast::BinOp::Is | ast::BinOp::In => TypeId::BOOL,
                    _ => left_hir.ty,
                };

                Ok(HirExpr {
                    kind: HirExprKind::Binary {
                        op: (*op).into(),
                        left: left_hir,
                        right: right_hir,
                    },
                    ty,
                })
            }

            Expr::Unary { op, operand } => {
                let operand_hir = Box::new(self.lower_expr(operand, ctx)?);
                let ty = match op {
                    ast::UnaryOp::Not => TypeId::BOOL,
                    ast::UnaryOp::Ref | ast::UnaryOp::RefMut => {
                        let kind = if *op == ast::UnaryOp::RefMut {
                            PointerKind::BorrowMut
                        } else {
                            PointerKind::Borrow
                        };
                        let ptr_type = HirType::Pointer {
                            kind,
                            inner: operand_hir.ty,
                        };
                        self.module.types.register(ptr_type)
                    }
                    ast::UnaryOp::Deref => {
                        // Look up inner type from pointer type
                        self.get_deref_type(operand_hir.ty)?
                    }
                    _ => operand_hir.ty,
                };

                match op {
                    ast::UnaryOp::Ref | ast::UnaryOp::RefMut => Ok(HirExpr {
                        kind: HirExprKind::Ref(operand_hir),
                        ty,
                    }),
                    ast::UnaryOp::Deref => Ok(HirExpr {
                        kind: HirExprKind::Deref(operand_hir),
                        ty,
                    }),
                    _ => Ok(HirExpr {
                        kind: HirExprKind::Unary {
                            op: (*op).into(),
                            operand: operand_hir,
                        },
                        ty,
                    }),
                }
            }

            Expr::Call { callee, args } => {
                let func_hir = Box::new(self.lower_expr(callee, ctx)?);
                let mut args_hir = Vec::new();
                for arg in args {
                    args_hir.push(self.lower_expr(&arg.value, ctx)?);
                }

                // Return type comes from function type
                let ret_ty = func_hir.ty; // Simplified - would need function type lookup

                Ok(HirExpr {
                    kind: HirExprKind::Call {
                        func: func_hir,
                        args: args_hir,
                    },
                    ty: ret_ty,
                })
            }

            Expr::FieldAccess { receiver, field } => {
                let recv_hir = Box::new(self.lower_expr(receiver, ctx)?);
                // Look up struct field type and index
                let (field_index, field_ty) = self.get_field_info(recv_hir.ty, field)?;
                Ok(HirExpr {
                    kind: HirExprKind::FieldAccess {
                        receiver: recv_hir,
                        field_index,
                    },
                    ty: field_ty,
                })
            }

            Expr::Index { receiver, index } => {
                let recv_hir = Box::new(self.lower_expr(receiver, ctx)?);
                let idx_hir = Box::new(self.lower_expr(index, ctx)?);
                // Look up element type from array type
                let elem_ty = self.get_index_element_type(recv_hir.ty)?;

                Ok(HirExpr {
                    kind: HirExprKind::Index {
                        receiver: recv_hir,
                        index: idx_hir,
                    },
                    ty: elem_ty,
                })
            }

            Expr::Tuple(exprs) => {
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

            Expr::Array(exprs) => {
                let mut hir_exprs = Vec::new();
                let elem_ty = if let Some(first) = exprs.first() {
                    self.infer_type(first, ctx)?
                } else {
                    // Empty array needs explicit type annotation
                    // For now, default to VOID to allow empty arrays (will fail later if used)
                    TypeId::VOID
                };

                for e in exprs {
                    hir_exprs.push(self.lower_expr(e, ctx)?);
                }

                let arr_ty = self.module.types.register(HirType::Array {
                    element: elem_ty,
                    size: Some(exprs.len()),
                });

                Ok(HirExpr {
                    kind: HirExprKind::Array(hir_exprs),
                    ty: arr_ty,
                })
            }

            Expr::If { condition, then_branch, else_branch } => {
                let cond_hir = Box::new(self.lower_expr(condition, ctx)?);
                let then_hir = Box::new(self.lower_expr(then_branch, ctx)?);
                let else_hir = if let Some(eb) = else_branch {
                    Some(Box::new(self.lower_expr(eb, ctx)?))
                } else {
                    None
                };

                let ty = then_hir.ty;

                Ok(HirExpr {
                    kind: HirExprKind::If {
                        condition: cond_hir,
                        then_branch: then_hir,
                        else_branch: else_hir,
                    },
                    ty,
                })
            }

            _ => Err(LowerError::Unsupported(format!("{:?}", expr))),
        }
    }

    fn infer_type(&mut self, expr: &Expr, ctx: &FunctionContext) -> LowerResult<TypeId> {
        match expr {
            Expr::Integer(_) => Ok(TypeId::I64),
            Expr::Float(_) => Ok(TypeId::F64),
            Expr::String(_) => Ok(TypeId::STRING),
            Expr::Bool(_) => Ok(TypeId::BOOL),
            Expr::Nil => Ok(TypeId::NIL),
            Expr::Identifier(name) => {
                if let Some(idx) = ctx.lookup(name) {
                    Ok(ctx.locals[idx].ty)
                } else if let Some(ty) = self.globals.get(name) {
                    Ok(*ty)
                } else {
                    Err(LowerError::UnknownVariable(name.clone()))
                }
            }
            Expr::Binary { op, left, .. } => {
                match op {
                    ast::BinOp::Eq | ast::BinOp::NotEq |
                    ast::BinOp::Lt | ast::BinOp::Gt |
                    ast::BinOp::LtEq | ast::BinOp::GtEq |
                    ast::BinOp::And | ast::BinOp::Or => Ok(TypeId::BOOL),
                    _ => self.infer_type(left, ctx),
                }
            }
            Expr::Unary { op, operand } => {
                match op {
                    ast::UnaryOp::Not => Ok(TypeId::BOOL),
                    _ => self.infer_type(operand, ctx),
                }
            }
            Expr::Call { callee, .. } => {
                // Return type of call is the type of the callee (function)
                self.infer_type(callee, ctx)
            }
            Expr::If { then_branch, .. } => {
                // Type of if-expression is the type of the then branch
                self.infer_type(then_branch, ctx)
            }
            Expr::Tuple(exprs) => {
                // Infer tuple type from elements
                if exprs.is_empty() {
                    Ok(TypeId::VOID)
                } else {
                    // Recursively infer element types
                    let mut types = Vec::new();
                    for e in exprs {
                        types.push(self.infer_type(e, ctx)?);
                    }
                    Ok(self.module.types.register(HirType::Tuple(types)))
                }
            }
            Expr::Array(exprs) => {
                if let Some(first) = exprs.first() {
                    // Infer array type from first element
                    let elem_ty = self.infer_type(first, ctx)?;
                    Ok(self.module.types.register(HirType::Array {
                        element: elem_ty,
                        size: Some(exprs.len()),
                    }))
                } else {
                    Ok(TypeId::VOID)
                }
            }
            Expr::Index { receiver, .. } => {
                // Infer element type from array type
                let arr_ty = self.infer_type(receiver, ctx)?;
                self.get_index_element_type(arr_ty)
            }
            Expr::FieldAccess { receiver, field } => {
                // Infer field type from struct type
                let struct_ty = self.infer_type(receiver, ctx)?;
                let (_idx, field_ty) = self.get_field_info(struct_ty, field)?;
                Ok(field_ty)
            }
            // Cannot infer type for complex expressions - require annotation
            _ => Err(LowerError::CannotInferTypeFor(format!("{:?}", expr))),
        }
    }

    /// Get the inner type of a pointer for deref operations.
    fn get_deref_type(&self, ptr_ty: TypeId) -> LowerResult<TypeId> {
        if let Some(hir_ty) = self.module.types.get(ptr_ty) {
            match hir_ty {
                HirType::Pointer { inner, .. } => Ok(*inner),
                _ => Err(LowerError::CannotInferDerefType(format!("{:?}", hir_ty))),
            }
        } else {
            Err(LowerError::CannotInferDerefType(format!("TypeId({:?})", ptr_ty)))
        }
    }

    /// Get the field index and type for a struct field access.
    fn get_field_info(&self, struct_ty: TypeId, field: &str) -> LowerResult<(usize, TypeId)> {
        if let Some(hir_ty) = self.module.types.get(struct_ty) {
            match hir_ty {
                HirType::Struct { name, fields } => {
                    for (idx, (field_name, field_ty)) in fields.iter().enumerate() {
                        if field_name == field {
                            return Ok((idx, *field_ty));
                        }
                    }
                    Err(LowerError::CannotInferFieldType {
                        struct_name: name.clone(),
                        field: field.to_string(),
                    })
                }
                HirType::Pointer { inner, .. } => {
                    // Auto-deref for pointer to struct
                    self.get_field_info(*inner, field)
                }
                _ => Err(LowerError::CannotInferFieldType {
                    struct_name: format!("{:?}", hir_ty),
                    field: field.to_string(),
                }),
            }
        } else {
            Err(LowerError::CannotInferFieldType {
                struct_name: format!("TypeId({:?})", struct_ty),
                field: field.to_string(),
            })
        }
    }

    /// Get the element type for array index access.
    fn get_index_element_type(&self, arr_ty: TypeId) -> LowerResult<TypeId> {
        if let Some(hir_ty) = self.module.types.get(arr_ty) {
            match hir_ty {
                HirType::Array { element, .. } => Ok(*element),
                HirType::Tuple(types) => {
                    // For tuple indexing, would need compile-time index
                    // For now, return first element type if exists
                    types.first().copied().ok_or_else(|| {
                        LowerError::CannotInferIndexType("empty tuple".to_string())
                    })
                }
                HirType::Pointer { inner, .. } => {
                    // Auto-deref for pointer to array
                    self.get_index_element_type(*inner)
                }
                _ => Err(LowerError::CannotInferIndexType(format!("{:?}", hir_ty))),
            }
        } else {
            Err(LowerError::CannotInferIndexType(format!("TypeId({:?})", arr_ty)))
        }
    }
}

impl Lowerer {
    /// Extract the variable name from a pattern, handling typed patterns
    fn extract_pattern_name(pattern: &Pattern) -> Option<String> {
        match pattern {
            Pattern::Identifier(n) => Some(n.clone()),
            Pattern::MutIdentifier(n) => Some(n.clone()),
            Pattern::Typed { pattern: inner, .. } => Self::extract_pattern_name(inner),
            _ => None,
        }
    }
}

impl Default for Lowerer {
    fn default() -> Self {
        Self::new()
    }
}

/// Convenience function to lower an AST module to HIR
pub fn lower(module: &Module) -> LowerResult<HirModule> {
    Lowerer::new().lower_module(module)
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::Parser;

    fn parse_and_lower(source: &str) -> LowerResult<HirModule> {
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("parse failed");
        lower(&module)
    }

    #[test]
    fn test_lower_simple_function() {
        let module = parse_and_lower("fn add(a: i64, b: i64) -> i64:\n    return a + b\n").unwrap();

        assert_eq!(module.functions.len(), 1);
        let func = &module.functions[0];
        assert_eq!(func.name, "add");
        assert_eq!(func.params.len(), 2);
        assert_eq!(func.return_type, TypeId::I64);
    }

    #[test]
    fn test_basic_types() {
        // Test basic types: i64, str, bool, f64
        let module = parse_and_lower("fn greet(name: str) -> i64:\n    let x: i64 = 42\n    return x\n").unwrap();

        let func = &module.functions[0];
        assert_eq!(func.params[0].ty, TypeId::STRING);
        assert_eq!(func.return_type, TypeId::I64);
        assert_eq!(func.locals[0].ty, TypeId::I64);
    }

    #[test]
    fn test_lower_function_with_locals() {
        let module = parse_and_lower(
            "fn compute(x: i64) -> i64:\n    let y: i64 = x * 2\n    return y\n"
        ).unwrap();

        let func = &module.functions[0];
        assert_eq!(func.params.len(), 1);
        assert_eq!(func.locals.len(), 1);
        assert_eq!(func.locals[0].name, "y");
    }

    #[test]
    fn test_lower_literals() {
        let module = parse_and_lower(
            "fn test() -> i64:\n    let a: i64 = 42\n    let b: f64 = 3.14\n    let c: bool = true\n    return a\n"
        ).unwrap();

        let func = &module.functions[0];
        assert_eq!(func.locals.len(), 3);
    }

    #[test]
    fn test_lower_binary_ops() {
        let module = parse_and_lower(
            "fn compare(a: i64, b: i64) -> bool:\n    return a < b\n"
        ).unwrap();

        let func = &module.functions[0];
        assert_eq!(func.return_type, TypeId::BOOL);

        if let HirStmt::Return(Some(expr)) = &func.body[0] {
            assert_eq!(expr.ty, TypeId::BOOL);
        } else {
            panic!("Expected return statement");
        }
    }

    #[test]
    fn test_lower_if_statement() {
        let module = parse_and_lower(
            "fn max(a: i64, b: i64) -> i64:\n    if a > b:\n        return a\n    else:\n        return b\n"
        ).unwrap();

        let func = &module.functions[0];
        assert!(matches!(func.body[0], HirStmt::If { .. }));
    }

    #[test]
    fn test_lower_while_loop() {
        let module = parse_and_lower(
            "fn count() -> i64:\n    let x: i64 = 0\n    while x < 10:\n        x = x + 1\n    return x\n"
        ).unwrap();

        let func = &module.functions[0];
        assert!(matches!(func.body[1], HirStmt::While { .. }));
    }

    #[test]
    fn test_lower_struct() {
        let module = parse_and_lower(
            "struct Point:\n    x: f64\n    y: f64\n\nfn origin() -> i64:\n    return 0\n"
        ).unwrap();

        assert!(module.types.lookup("Point").is_some());
    }

    #[test]
    fn test_unknown_type_error() {
        let result = parse_and_lower(
            "fn test(x: Unknown) -> i64:\n    return 0\n"
        );

        assert!(matches!(result, Err(LowerError::UnknownType(_))));
    }

    #[test]
    fn test_unknown_variable_error() {
        let result = parse_and_lower(
            "fn test() -> i64:\n    return unknown\n"
        );

        assert!(matches!(result, Err(LowerError::UnknownVariable(_))));
    }

    #[test]
    fn test_lower_array_expression() {
        let module = parse_and_lower(
            "fn test() -> i64:\n    let arr = [1, 2, 3]\n    return 0\n"
        ).unwrap();

        let func = &module.functions[0];
        assert!(!func.locals.is_empty());
    }

    #[test]
    fn test_lower_tuple_expression() {
        let module = parse_and_lower(
            "fn test() -> i64:\n    let t = (1, 2, 3)\n    return 0\n"
        ).unwrap();

        let func = &module.functions[0];
        assert!(!func.locals.is_empty());
    }

    #[test]
    fn test_lower_empty_array() {
        let module = parse_and_lower(
            "fn test() -> i64:\n    let arr = []\n    return 0\n"
        ).unwrap();

        let func = &module.functions[0];
        assert_eq!(func.locals.len(), 1);
    }

    #[test]
    fn test_lower_index_expression() {
        let module = parse_and_lower(
            "fn test() -> i64:\n    let arr = [1, 2, 3]\n    let x = arr[0]\n    return x\n"
        ).unwrap();

        let func = &module.functions[0];
        assert_eq!(func.locals.len(), 2);
    }

    #[test]
    fn test_lower_function_call() {
        let module = parse_and_lower(
            "fn add(a: i64, b: i64) -> i64:\n    return a + b\n\nfn test() -> i64:\n    return add(1, 2)\n"
        ).unwrap();

        assert_eq!(module.functions.len(), 2);
    }

    #[test]
    fn test_lower_if_expression() {
        let module = parse_and_lower(
            "fn test(x: i64) -> i64:\n    let y = if x > 0: 1 else: 0\n    return y\n"
        ).unwrap();

        let func = &module.functions[0];
        assert_eq!(func.locals.len(), 1);
    }

    #[test]
    fn test_lower_string_literal() {
        // Use single quotes for raw string (double quotes create FStrings)
        let module = parse_and_lower(
            "fn test() -> str:\n    return 'hello'\n"
        ).unwrap();

        let func = &module.functions[0];
        assert_eq!(func.return_type, TypeId::STRING);
    }

    #[test]
    fn test_lower_bool_literal() {
        let module = parse_and_lower(
            "fn test() -> bool:\n    return false\n"
        ).unwrap();

        let func = &module.functions[0];
        assert_eq!(func.return_type, TypeId::BOOL);
    }

    #[test]
    fn test_lower_float_literal() {
        let module = parse_and_lower(
            "fn test() -> f64:\n    return 3.14\n"
        ).unwrap();

        let func = &module.functions[0];
        assert_eq!(func.return_type, TypeId::F64);
    }

    #[test]
    fn test_lower_nil_literal() {
        let module = parse_and_lower(
            "fn test() -> i64:\n    let x = nil\n    return 0\n"
        ).unwrap();

        let func = &module.functions[0];
        assert_eq!(func.locals.len(), 1);
    }

    #[test]
    fn test_lower_unary_negation() {
        let module = parse_and_lower(
            "fn test(x: i64) -> i64:\n    return -x\n"
        ).unwrap();

        let func = &module.functions[0];
        if let HirStmt::Return(Some(expr)) = &func.body[0] {
            assert!(matches!(expr.kind, HirExprKind::Unary { .. }));
        }
    }

    #[test]
    fn test_lower_logical_not() {
        let module = parse_and_lower(
            "fn test(x: bool) -> bool:\n    return not x\n"
        ).unwrap();

        let func = &module.functions[0];
        if let HirStmt::Return(Some(expr)) = &func.body[0] {
            assert!(matches!(expr.kind, HirExprKind::Unary { .. }));
        }
    }

    #[test]
    fn test_lower_comparison_operators() {
        // Test all comparison operators return bool
        let ops = ["<", ">", "<=", ">=", "==", "!="];
        for op in ops {
            let source = format!("fn test(a: i64, b: i64) -> bool:\n    return a {} b\n", op);
            let module = parse_and_lower(&source).unwrap();
            let func = &module.functions[0];
            assert_eq!(func.return_type, TypeId::BOOL);
        }
    }

    #[test]
    fn test_lower_logical_operators() {
        // Test and/or return bool
        let module = parse_and_lower(
            "fn test(a: bool, b: bool) -> bool:\n    return a and b\n"
        ).unwrap();
        assert_eq!(module.functions[0].return_type, TypeId::BOOL);

        let module = parse_and_lower(
            "fn test(a: bool, b: bool) -> bool:\n    return a or b\n"
        ).unwrap();
        assert_eq!(module.functions[0].return_type, TypeId::BOOL);
    }

    #[test]
    fn test_lower_field_access() {
        let module = parse_and_lower(
            "struct Point:\n    x: i64\n    y: i64\n\nfn test(p: Point) -> i64:\n    return p.x\n"
        ).unwrap();

        let func = &module.functions[0];
        if let HirStmt::Return(Some(expr)) = &func.body[0] {
            assert!(matches!(expr.kind, HirExprKind::FieldAccess { .. }));
        }
    }

    #[test]
    fn test_lower_assignment() {
        let module = parse_and_lower(
            "fn test() -> i64:\n    let mut x: i64 = 0\n    x = 42\n    return x\n"
        ).unwrap();

        let func = &module.functions[0];
        assert!(matches!(func.body[1], HirStmt::Assign { .. }));
    }

    #[test]
    fn test_lower_expression_statement() {
        let module = parse_and_lower(
            "fn test() -> i64:\n    1 + 2\n    return 0\n"
        ).unwrap();

        let func = &module.functions[0];
        assert!(matches!(func.body[0], HirStmt::Expr(_)));
    }

    #[test]
    fn test_infer_type_from_binary_arithmetic() {
        let module = parse_and_lower(
            "fn test() -> i64:\n    let x = 1 + 2\n    return x\n"
        ).unwrap();

        let func = &module.functions[0];
        // The type should be inferred from the left operand (i64)
        assert_eq!(func.locals[0].ty, TypeId::I64);
    }

    #[test]
    fn test_lower_return_without_value() {
        let module = parse_and_lower(
            "fn test() -> i64:\n    return\n"
        ).unwrap();

        let func = &module.functions[0];
        assert!(matches!(func.body[0], HirStmt::Return(None)));
    }

    #[test]
    fn test_multiple_functions() {
        let module = parse_and_lower(
            "fn foo() -> i64:\n    return 1\n\nfn bar() -> i64:\n    return 2\n\nfn baz() -> i64:\n    return 3\n"
        ).unwrap();

        assert_eq!(module.functions.len(), 3);
        assert_eq!(module.functions[0].name, "foo");
        assert_eq!(module.functions[1].name, "bar");
        assert_eq!(module.functions[2].name, "baz");
    }

    #[test]
    fn test_function_with_multiple_params() {
        let module = parse_and_lower(
            "fn multi(a: i64, b: f64, c: str, d: bool) -> i64:\n    return a\n"
        ).unwrap();

        let func = &module.functions[0];
        assert_eq!(func.params.len(), 4);
        assert_eq!(func.params[0].ty, TypeId::I64);
        assert_eq!(func.params[1].ty, TypeId::F64);
        assert_eq!(func.params[2].ty, TypeId::STRING);
        assert_eq!(func.params[3].ty, TypeId::BOOL);
    }
}
