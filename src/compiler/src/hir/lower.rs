use std::collections::HashMap;

use simple_parser::{self as ast, Module, Node, Expr, Type, Pattern};
use thiserror::Error;

use super::types::*;

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
        self.locals.push(LocalVar { name: name.clone(), ty, is_mutable });
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
                _ => {}
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
        for param in &f.params {
            let ty = if let Some(t) = &param.ty {
                self.resolve_type(t)?
            } else {
                TypeId::UNKNOWN
            };
            ctx.add_local(param.name.clone(), ty, param.is_mutable);
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
            is_public: f.is_public,
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

                let local_index = ctx.add_local(name, ty, let_stmt.is_mutable);

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
                    ast::UnaryOp::Ref => {
                        let ptr_type = HirType::Pointer {
                            kind: PointerKind::Unique,
                            inner: operand_hir.ty,
                        };
                        self.module.types.register(ptr_type)
                    }
                    ast::UnaryOp::Deref => {
                        // Would need type lookup
                        TypeId::UNKNOWN
                    }
                    _ => operand_hir.ty,
                };

                match op {
                    ast::UnaryOp::Ref => Ok(HirExpr {
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
                // Would need struct field lookup
                Ok(HirExpr {
                    kind: HirExprKind::FieldAccess {
                        receiver: recv_hir,
                        field_index: 0, // Placeholder
                    },
                    ty: TypeId::UNKNOWN,
                })
            }

            Expr::Index { receiver, index } => {
                let recv_hir = Box::new(self.lower_expr(receiver, ctx)?);
                let idx_hir = Box::new(self.lower_expr(index, ctx)?);

                Ok(HirExpr {
                    kind: HirExprKind::Index {
                        receiver: recv_hir,
                        index: idx_hir,
                    },
                    ty: TypeId::UNKNOWN,
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
                    TypeId::UNKNOWN
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
            _ => Ok(TypeId::UNKNOWN),
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
}
