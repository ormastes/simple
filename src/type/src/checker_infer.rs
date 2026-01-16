impl TypeChecker {
    pub fn infer_expr(&mut self, expr: &Expr) -> Result<Type, TypeError> {
        match expr {
            Expr::Integer(_) => Ok(Type::Int),
            Expr::Float(_) => Ok(Type::Float),
            Expr::String(_) => Ok(Type::Str),
            Expr::FString(parts) => {
                use simple_parser::ast::FStringPart;
                for part in parts {
                    if let FStringPart::Expr(e) = part {
                        let _ = self.infer_expr(e)?;
                    }
                }
                Ok(Type::Str)
            }
            Expr::Bool(_) => Ok(Type::Bool),
            Expr::Nil => Ok(Type::Nil),
            Expr::Identifier(name) => self
                .env
                .get(name)
                .cloned()
                .ok_or_else(|| TypeError::Undefined(format!("undefined identifier: {}", name))),
            Expr::MacroInvocation { name, args } => {
                for arg in args {
                    let simple_parser::ast::MacroArg::Expr(expr) = arg;
                    let _ = self.infer_expr(expr)?;
                }
                if !self.available_macros.contains(name) {
                    return Err(TypeError::Other(format!(
                        "macro '{}' must be defined before use",
                        name
                    )));
                }
                let macro_def = self
                    .macros
                    .get(name)
                    .cloned()
                    .ok_or_else(|| TypeError::Undefined(format!("undefined macro: {}", name)))?;
                let const_bindings = self.build_macro_const_bindings(&macro_def, args);
                self.apply_macro_intros(&macro_def, &const_bindings)?;
                Ok(self.macro_return_type(&macro_def))
            }
            Expr::Binary { left, right, op } => {
                let left_ty = self.infer_expr(left)?;
                let right_ty = self.infer_expr(right)?;

                match op {
                    // Arithmetic operators: both operands should be numeric, result is numeric
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Mod
                    | BinOp::Pow
                    | BinOp::FloorDiv
                    | BinOp::MatMul => { // Simple Math #1930-#1939: matrix multiplication
                        // Unify operands to ensure they're compatible
                        let _ = self.unify(&left_ty, &right_ty);
                        Ok(self.resolve(&left_ty))
                    }
                    // Comparison operators: result is always Bool
                    BinOp::Eq
                    | BinOp::NotEq
                    | BinOp::Lt
                    | BinOp::LtEq
                    | BinOp::Gt
                    | BinOp::GtEq => {
                        // Operands should be comparable (same type)
                        let _ = self.unify(&left_ty, &right_ty);
                        Ok(Type::Bool)
                    }
                    // Logical operators: both operands should be Bool, result is Bool
                    BinOp::And | BinOp::Or => {
                        let _ = self.unify(&left_ty, &Type::Bool);
                        let _ = self.unify(&right_ty, &Type::Bool);
                        Ok(Type::Bool)
                    }
                    // Bitwise operators: both operands should be Int
                    BinOp::BitAnd
                    | BinOp::BitOr
                    | BinOp::BitXor
                    | BinOp::ShiftLeft
                    | BinOp::ShiftRight => {
                        let _ = self.unify(&left_ty, &Type::Int);
                        let _ = self.unify(&right_ty, &Type::Int);
                        Ok(Type::Int)
                    }
                    // Is and In operators
                    BinOp::Is | BinOp::In => Ok(Type::Bool),
                }
            }
            Expr::Unary { op, operand } => {
                use simple_parser::ast::UnaryOp;
                let operand_ty = self.infer_expr(operand)?;
                match op {
                    UnaryOp::Ref => Ok(Type::Borrow(Box::new(operand_ty))),
                    UnaryOp::RefMut => Ok(Type::BorrowMut(Box::new(operand_ty))),
                    UnaryOp::Deref => {
                        // Dereferencing a borrow gives the inner type
                        match operand_ty {
                            Type::Borrow(inner) | Type::BorrowMut(inner) => Ok(*inner),
                            _ => Ok(operand_ty), // For other types, just pass through
                        }
                    }
                    UnaryOp::Neg => {
                        let _ = self.unify(&operand_ty, &Type::Int);
                        Ok(Type::Int)
                    }
                    UnaryOp::Not => Ok(Type::Bool),
                    UnaryOp::BitNot => {
                        let _ = self.unify(&operand_ty, &Type::Int);
                        Ok(Type::Int)
                    }
                    UnaryOp::ChannelRecv => {
                        // Channel receive: extract value type from Channel<T>
                        // Returns T when receiving from a channel
                        let resolved = self.resolve(&operand_ty);
                        match resolved {
                            Type::Generic { name, args } if name == "Channel" && !args.is_empty() => {
                                // Channel<T> -> T
                                Ok(args[0].clone())
                            }
                            Type::Named(name) if name == "Channel" => {
                                // Unparameterized Channel -> fresh type variable
                                Ok(self.fresh_var())
                            }
                            Type::Var(_) => {
                                // Type variable - create constraint that it must be Channel<T>
                                let inner = self.fresh_var();
                                let channel_ty = Type::Generic {
                                    name: "Channel".to_string(),
                                    args: vec![inner.clone()],
                                };
                                let _ = self.unify(&operand_ty, &channel_ty);
                                Ok(inner)
                            }
                            _ => {
                                // Not a channel type - return fresh var and let unification fail later
                                Ok(self.fresh_var())
                            }
                        }
                    }
                }
            }
            Expr::Call { callee, args } => {
                let callee_ty = self.infer_expr(callee)?;
                let mut arg_types = Vec::new();
                for arg in args {
                    arg_types.push(self.infer_expr(&arg.value)?);
                }
                // If callee has a function type, use its return type
                let result_ty = self.fresh_var();
                match self.resolve(&callee_ty) {
                    Type::Function { params, ret } => {
                        // Unify argument types with parameter types
                        for (arg_ty, param_ty) in arg_types.iter().zip(params.iter()) {
                            let _ = self.unify(arg_ty, param_ty);
                        }
                        Ok(*ret)
                    }
                    _ => Ok(result_ty),
                }
            }
            Expr::Array(items) => {
                if items.is_empty() {
                    // Empty array has unknown element type
                    let elem_ty = self.fresh_var();
                    Ok(Type::Array(Box::new(elem_ty)))
                } else {
                    // Infer element type from first item, unify with rest
                    let first_ty = self.infer_expr(&items[0])?;
                    for item in items.iter().skip(1) {
                        let item_ty = self.infer_expr(item)?;
                        let _ = self.unify(&first_ty, &item_ty);
                    }
                    Ok(Type::Array(Box::new(self.resolve(&first_ty))))
                }
            }
            Expr::Index { receiver, index } => {
                let recv_ty = self.infer_expr(receiver)?;
                let idx_ty = self.infer_expr(index)?;
                // Index should be Int for arrays
                let _ = self.unify(&idx_ty, &Type::Int);
                // Result type depends on receiver
                match self.resolve(&recv_ty) {
                    Type::Array(elem) => Ok(*elem),
                    Type::Str => Ok(Type::Str), // String indexing returns string/char
                    Type::Dict { value, .. } => Ok(*value),
                    Type::Tuple(_types) => {
                        // Tuple indexing - type depends on index literal
                        // For now, return fresh var since we don't know which element
                        Ok(self.fresh_var())
                    }
                    _ => Ok(self.fresh_var()),
                }
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                let cond_ty = self.infer_expr(condition)?;
                // Condition should be Bool
                let _ = self.unify(&cond_ty, &Type::Bool);
                let then_ty = self.infer_expr(then_branch)?;
                if let Some(else_b) = else_branch {
                    let else_ty = self.infer_expr(else_b)?;
                    // Both branches should have same type
                    let _ = self.unify(&then_ty, &else_ty);
                }
                Ok(self.resolve(&then_ty))
            }
            Expr::Match { subject, arms } => {
                let _ = self.infer_expr(subject)?;
                let result_ty = self.fresh_var();
                self.check_match_arms(arms)?;
                Ok(result_ty)
            }
            Expr::FieldAccess { receiver, .. } => {
                let _ = self.infer_expr(receiver)?;
                Ok(self.fresh_var())
            }
            Expr::MethodCall { receiver, args, .. } => {
                let _ = self.infer_expr(receiver)?;
                for arg in args {
                    let _ = self.infer_expr(&arg.value)?;
                }
                Ok(self.fresh_var())
            }
            Expr::StructInit { fields, .. } => {
                for (_, expr) in fields {
                    let _ = self.infer_expr(expr)?;
                }
                Ok(self.fresh_var())
            }
            Expr::Path(_) => Ok(self.fresh_var()),
            Expr::Range { start, end, .. } => {
                if let Some(s) = start {
                    let _ = self.infer_expr(s)?;
                }
                if let Some(e) = end {
                    let _ = self.infer_expr(e)?;
                }
                Ok(self.fresh_var())
            }
            Expr::Dict(entries) => {
                for (k, v) in entries {
                    let _ = self.infer_expr(k)?;
                    let _ = self.infer_expr(v)?;
                }
                Ok(self.fresh_var())
            }
            _ => Ok(self.fresh_var()),
        }
    }
}
