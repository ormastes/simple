/// Look up the family name for a unit suffix from the thread-local registry
fn lookup_unit_family(suffix: &str) -> Option<String> {
    // First try direct lookup
    if let Some(family) = UNIT_SUFFIX_TO_FAMILY.with(|cell| cell.borrow().get(suffix).cloned()) {
        return Some(family);
    }
    // Try SI prefix decomposition
    if let Some((_multiplier, _base, family)) = decompose_si_prefix(suffix) {
        return Some(family);
    }
    None
}

/// Look up unit family with SI prefix info
/// Returns (family_name, si_multiplier, base_suffix) if SI prefix was used
fn lookup_unit_family_with_si(suffix: &str) -> (Option<String>, Option<f64>, Option<String>) {
    // First try direct lookup
    if let Some(family) = UNIT_SUFFIX_TO_FAMILY.with(|cell| cell.borrow().get(suffix).cloned()) {
        return (Some(family), None, None);
    }
    // Try SI prefix decomposition
    if let Some((multiplier, base, family)) = decompose_si_prefix(suffix) {
        return (Some(family), Some(multiplier), Some(base));
    }
    (None, None, None)
}

/// Perform a binary operation on the inner values of two units
fn evaluate_unit_binary_inner(
    left: &Value,
    right: &Value,
    op: BinOp,
) -> Result<Value, CompileError> {
    match op {
        BinOp::Add => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l + r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Float(l + r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Float(*l as f64 + r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Float(l + *r as f64)),
            _ => Err(CompileError::Semantic(format!(
                "cannot add unit values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        BinOp::Sub => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l - r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Float(l - r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Float(*l as f64 - r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Float(l - *r as f64)),
            _ => Err(CompileError::Semantic(format!(
                "cannot subtract unit values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        BinOp::Mul => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l * r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Float(l * r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Float(*l as f64 * r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Float(l * *r as f64)),
            _ => Err(CompileError::Semantic(format!(
                "cannot multiply unit values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        BinOp::Div => match (left, right) {
            (Value::Int(l), Value::Int(r)) => {
                if *r == 0 {
                    Err(CompileError::Semantic("division by zero".into()))
                } else {
                    Ok(Value::Int(l / r))
                }
            }
            (Value::Float(l), Value::Float(r)) => {
                if *r == 0.0 {
                    Err(CompileError::Semantic("division by zero".into()))
                } else {
                    Ok(Value::Float(l / r))
                }
            }
            (Value::Int(l), Value::Float(r)) => {
                if *r == 0.0 {
                    Err(CompileError::Semantic("division by zero".into()))
                } else {
                    Ok(Value::Float(*l as f64 / r))
                }
            }
            (Value::Float(l), Value::Int(r)) => {
                if *r == 0 {
                    Err(CompileError::Semantic("division by zero".into()))
                } else {
                    Ok(Value::Float(l / *r as f64))
                }
            }
            _ => Err(CompileError::Semantic(format!(
                "cannot divide unit values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        BinOp::Mod => match (left, right) {
            (Value::Int(l), Value::Int(r)) => {
                if *r == 0 {
                    Err(CompileError::Semantic("modulo by zero".into()))
                } else {
                    Ok(Value::Int(l % r))
                }
            }
            _ => Err(CompileError::Semantic(format!(
                "modulo only supported for integer unit values, got {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        // Comparison operations return bool, not unit
        BinOp::Eq => Ok(Value::Bool(left == right)),
        BinOp::NotEq => Ok(Value::Bool(left != right)),
        BinOp::Lt => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l < r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l < r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Bool((*l as f64) < *r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Bool(*l < (*r as f64))),
            _ => Err(CompileError::Semantic(format!(
                "cannot compare unit values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        BinOp::Gt => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l > r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l > r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Bool((*l as f64) > *r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Bool(*l > (*r as f64))),
            _ => Err(CompileError::Semantic(format!(
                "cannot compare unit values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        BinOp::LtEq => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l <= r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l <= r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Bool((*l as f64) <= *r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Bool(*l <= (*r as f64))),
            _ => Err(CompileError::Semantic(format!(
                "cannot compare unit values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        BinOp::GtEq => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l >= r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l >= r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Bool((*l as f64) >= *r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Bool(*l >= (*r as f64))),
            _ => Err(CompileError::Semantic(format!(
                "cannot compare unit values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        _ => Err(CompileError::Semantic(format!(
            "unsupported binary operation {:?} on unit values",
            op
        ))),
    }
}

/// Perform a unary operation on the inner value of a unit
fn evaluate_unit_unary_inner(value: &Value, op: UnaryOp) -> Result<Value, CompileError> {
    match op {
        UnaryOp::Neg => match value {
            Value::Int(v) => Ok(Value::Int(-v)),
            Value::Float(v) => Ok(Value::Float(-v)),
            _ => Err(CompileError::Semantic(format!(
                "cannot negate unit value of type {}",
                value.type_name()
            ))),
        },
        UnaryOp::Not => Err(CompileError::Semantic(
            "cannot apply logical NOT to unit value".into(),
        )),
        UnaryOp::BitNot => Err(CompileError::Semantic(
            "cannot apply bitwise NOT to unit value".into(),
        )),
        _ => Err(CompileError::Semantic(format!(
            "unsupported unary operation {:?} on unit value",
            op
        ))),
    }
}

/// Evaluate a constant expression at compile time
#[instrument(skip(env, functions, classes, enums, impl_methods))]
pub(crate) fn evaluate_expr(
    expr: &Expr,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    match expr {
        Expr::Integer(value) => Ok(Value::Int(*value)),
        Expr::TypedInteger(value, suffix) => {
            use simple_parser::token::NumericSuffix;
            match suffix {
                NumericSuffix::Unit(unit_name) => {
                    // Create a Unit value for unit-suffixed integers
                    // Look up family from thread-local registry, with SI prefix support
                    let (family, si_multiplier, _base_suffix) = lookup_unit_family_with_si(unit_name);
                    // Apply SI prefix multiplier if present
                    let final_value = if let Some(mult) = si_multiplier {
                        // Convert to float and apply multiplier
                        Value::Float(*value as f64 * mult)
                    } else {
                        Value::Int(*value)
                    };
                    Ok(Value::Unit {
                        value: Box::new(final_value),
                        suffix: unit_name.clone(),
                        family,
                    })
                }
                _ => {
                    // For primitive type suffixes (i8, i32, etc.), just use the value
                    Ok(Value::Int(*value))
                }
            }
        }
        Expr::Float(value) => Ok(Value::Float(*value)),
        Expr::TypedFloat(value, suffix) => {
            use simple_parser::token::NumericSuffix;
            match suffix {
                NumericSuffix::Unit(unit_name) => {
                    // Create a Unit value for unit-suffixed floats, with SI prefix support
                    let (family, si_multiplier, _base_suffix) = lookup_unit_family_with_si(unit_name);
                    // Apply SI prefix multiplier if present
                    let final_value = if let Some(mult) = si_multiplier {
                        *value * mult
                    } else {
                        *value
                    };
                    Ok(Value::Unit {
                        value: Box::new(Value::Float(final_value)),
                        suffix: unit_name.clone(),
                        family,
                    })
                }
                _ => {
                    // For primitive type suffixes (f32, f64), just use the value
                    Ok(Value::Float(*value))
                }
            }
        }
        Expr::Bool(b) => Ok(Value::Bool(*b)),
        Expr::Nil => Ok(Value::Nil),
        Expr::String(s) => Ok(Value::Str(s.clone())),
        Expr::TypedString(s, suffix) => {
            // Create a Unit value for unit-suffixed strings (e.g., "127.0.0.1"_ip)
            let family = lookup_unit_family(suffix);
            Ok(Value::Unit {
                value: Box::new(Value::Str(s.clone())),
                suffix: suffix.clone(),
                family,
            })
        }
        Expr::FString(parts) => {
            let mut out = String::new();
            for part in parts {
                match part {
                    FStringPart::Literal(lit) => out.push_str(lit),
                    FStringPart::Expr(e) => {
                        let v = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                        out.push_str(&v.to_display_string());
                    }
                }
            }
            Ok(Value::Str(out))
        }
        Expr::Symbol(s) => Ok(Value::Symbol(s.clone())),
        Expr::Identifier(name) => {
            // Check for Option::None literal using type-safe variant
            if name == OptionVariant::None.as_str() {
                return Ok(Value::none());
            }
            // First check env for local variables and closures
            if let Some(val) = env.get(name) {
                return Ok(val.clone());
            }
            // Then check functions for top-level function definitions
            // Return as Value::Function for first-class function usage
            if let Some(func) = functions.get(name) {
                return Ok(Value::Function {
                    name: name.clone(),
                    def: Box::new(func.clone()),
                    captured_env: Env::new(), // Top-level functions don't capture
                });
            }
            // Check classes - return as Constructor for constructor polymorphism
            if classes.contains_key(name) {
                return Ok(Value::Constructor {
                    class_name: name.clone(),
                });
            }
            // Collect all known names for typo suggestion
            let known_names: Vec<&str> = env
                .keys()
                .map(|s| s.as_str())
                .chain(functions.keys().map(|s| s.as_str()))
                .chain(classes.keys().map(|s| s.as_str()))
                .collect();
            let mut msg = format!("undefined variable: {name}");
            if let Some(suggestion) = crate::error::typo::format_suggestion(name, known_names) {
                msg.push_str(&format!("; {}", suggestion));
            }
            Err(CompileError::Semantic(msg))
        }
        Expr::New { kind, expr } => {
            let inner = evaluate_expr(expr, env, functions, classes, enums, impl_methods)?;
            match kind {
                PointerKind::Unique => Ok(Value::Unique(ManualUniqueValue::new(inner))),
                PointerKind::Shared => Ok(Value::Shared(ManualSharedValue::new(inner))),
                PointerKind::Weak => {
                    if let Value::Shared(shared) = inner {
                        Ok(Value::Weak(ManualWeakValue::new_from_shared(&shared)))
                    } else {
                        Err(CompileError::Semantic(
                            "new - expects a shared pointer to create a weak reference".into(),
                        ))
                    }
                }
                PointerKind::Handle => Ok(Value::Handle(ManualHandleValue::new(inner))),
                PointerKind::Borrow => Ok(Value::Borrow(BorrowValue::new(inner))),
                PointerKind::BorrowMut => Ok(Value::BorrowMut(BorrowMutValue::new(inner))),
            }
        }
        Expr::Binary { op, left, right } => {
            let left_val = evaluate_expr(left, env, functions, classes, enums, impl_methods)?;
            let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)?;

            // Check for unit arithmetic type safety
            match (&left_val, &right_val) {
                (
                    Value::Unit { value: lv, suffix: ls, family: lf },
                    Value::Unit { value: rv, suffix: rs, family: rf },
                ) => {
                    // Both operands are units - check if operation is allowed
                    let left_family = lf.as_ref().map(|s| s.as_str()).unwrap_or(ls.as_str());
                    let right_family = rf.as_ref().map(|s| s.as_str()).unwrap_or(rs.as_str());

                    match check_unit_binary_op(left_family, right_family, *op) {
                        Ok(result_family) => {
                            // Operation allowed - perform it on inner values
                            let result_val = evaluate_unit_binary_inner(lv, rv, *op)?;
                            // Return unit with result family (or left family if same-family operation)
                            let result_suffix = if let Some(ref fam) = result_family {
                                fam.clone()
                            } else {
                                ls.clone()
                            };
                            return Ok(Value::Unit {
                                value: Box::new(result_val),
                                suffix: result_suffix,
                                family: result_family.or_else(|| lf.clone()),
                            });
                        }
                        Err(err) => {
                            return Err(CompileError::Semantic(err));
                        }
                    }
                }
                // Mixed unit/non-unit operations: allow scaling (mul/div)
                (Value::Unit { value, suffix, family }, other)
                | (other, Value::Unit { value, suffix, family })
                    if matches!(op, BinOp::Mul | BinOp::Div) =>
                {
                    // Scaling: unit * scalar or scalar * unit (or division)
                    let inner_result = evaluate_unit_binary_inner(value, other, *op)?;
                    return Ok(Value::Unit {
                        value: Box::new(inner_result),
                        suffix: suffix.clone(),
                        family: family.clone(),
                    });
                }
                // Mixed unit/non-unit for non-scaling ops is an error
                (Value::Unit { suffix: ls, .. }, _) => {
                    if !matches!(op, BinOp::Eq | BinOp::NotEq) {
                        return Err(CompileError::Semantic(format!(
                            "cannot apply {:?} between unit '{}' and non-unit value",
                            op, ls
                        )));
                    }
                    // Fall through for equality comparison
                }
                (_, Value::Unit { suffix: rs, .. }) => {
                    if !matches!(op, BinOp::Eq | BinOp::NotEq) {
                        return Err(CompileError::Semantic(format!(
                            "cannot apply {:?} between non-unit value and unit '{}'",
                            op, rs
                        )));
                    }
                    // Fall through for equality comparison
                }
                _ => {} // Neither is a unit - fall through to normal handling
            }

            // Standard binary operation handling (for non-unit operations)
            // Helper to determine if we should use float arithmetic
            let use_float = matches!(&left_val, Value::Float(_)) || matches!(&right_val, Value::Float(_));

            match op {
                BinOp::Add => match (&left_val, &right_val) {
                    (Value::Str(a), Value::Str(b)) => Ok(Value::Str(format!("{a}{b}"))),
                    (Value::Str(a), b) => Ok(Value::Str(format!("{a}{}", b.to_display_string()))),
                    (a, Value::Str(b)) => Ok(Value::Str(format!("{}{}", a.to_display_string(), b))),
                    _ if use_float => Ok(Value::Float(left_val.as_float()? + right_val.as_float()?)),
                    _ => Ok(Value::Int(left_val.as_int()? + right_val.as_int()?)),
                },
                BinOp::Sub => {
                    if use_float {
                        Ok(Value::Float(left_val.as_float()? - right_val.as_float()?))
                    } else {
                        Ok(Value::Int(left_val.as_int()? - right_val.as_int()?))
                    }
                }
                BinOp::Mul => {
                    if use_float {
                        Ok(Value::Float(left_val.as_float()? * right_val.as_float()?))
                    } else {
                        Ok(Value::Int(left_val.as_int()? * right_val.as_int()?))
                    }
                }
                BinOp::Div => {
                    if use_float {
                        let r = right_val.as_float()?;
                        if r == 0.0 {
                            Err(CompileError::Semantic("division by zero".into()))
                        } else {
                            Ok(Value::Float(left_val.as_float()? / r))
                        }
                    } else {
                        let r = right_val.as_int()?;
                        if r == 0 {
                            Err(CompileError::Semantic("division by zero".into()))
                        } else {
                            Ok(Value::Int(left_val.as_int()? / r))
                        }
                    }
                }
                BinOp::Mod => {
                    if use_float {
                        let r = right_val.as_float()?;
                        if r == 0.0 {
                            Err(CompileError::Semantic("modulo by zero".into()))
                        } else {
                            Ok(Value::Float(left_val.as_float()? % r))
                        }
                    } else {
                        let r = right_val.as_int()?;
                        if r == 0 {
                            Err(CompileError::Semantic("modulo by zero".into()))
                        } else {
                            Ok(Value::Int(left_val.as_int()? % r))
                        }
                    }
                }
                BinOp::Eq => Ok(Value::Bool(left_val == right_val)),
                BinOp::NotEq => Ok(Value::Bool(left_val != right_val)),
                BinOp::Lt => {
                    if use_float {
                        Ok(Value::Bool(left_val.as_float()? < right_val.as_float()?))
                    } else {
                        Ok(Value::Bool(left_val.as_int()? < right_val.as_int()?))
                    }
                }
                BinOp::Gt => {
                    if use_float {
                        Ok(Value::Bool(left_val.as_float()? > right_val.as_float()?))
                    } else {
                        Ok(Value::Bool(left_val.as_int()? > right_val.as_int()?))
                    }
                }
                BinOp::LtEq => {
                    if use_float {
                        Ok(Value::Bool(left_val.as_float()? <= right_val.as_float()?))
                    } else {
                        Ok(Value::Bool(left_val.as_int()? <= right_val.as_int()?))
                    }
                }
                BinOp::GtEq => {
                    if use_float {
                        Ok(Value::Bool(left_val.as_float()? >= right_val.as_float()?))
                    } else {
                        Ok(Value::Bool(left_val.as_int()? >= right_val.as_int()?))
                    }
                }
                BinOp::Is => Ok(Value::Bool(left_val == right_val)),
                BinOp::And => Ok(Value::Bool(left_val.truthy() && right_val.truthy())),
                BinOp::Or => Ok(Value::Bool(left_val.truthy() || right_val.truthy())),
                BinOp::Pow => {
                    if use_float {
                        Ok(Value::Float(left_val.as_float()?.powf(right_val.as_float()?)))
                    } else {
                        let base = left_val.as_int()?;
                        let exp = right_val.as_int()?;
                        if exp < 0 {
                            Err(CompileError::Semantic(
                                "negative exponent not supported for integers".into(),
                            ))
                        } else {
                            Ok(Value::Int(base.pow(exp as u32)))
                        }
                    }
                }
                BinOp::FloorDiv => {
                    let r = right_val.as_int()?;
                    if r == 0 {
                        Err(CompileError::Semantic("floor division by zero".into()))
                    } else {
                        let l = left_val.as_int()?;
                        // Floor division: always round towards negative infinity
                        Ok(Value::Int(l.div_euclid(r)))
                    }
                }
                BinOp::BitAnd => Ok(Value::Int(left_val.as_int()? & right_val.as_int()?)),
                BinOp::BitOr => Ok(Value::Int(left_val.as_int()? | right_val.as_int()?)),
                BinOp::BitXor => Ok(Value::Int(left_val.as_int()? ^ right_val.as_int()?)),
                BinOp::ShiftLeft => Ok(Value::Int(left_val.as_int()? << right_val.as_int()?)),
                BinOp::ShiftRight => Ok(Value::Int(left_val.as_int()? >> right_val.as_int()?)),
                BinOp::In => {
                    // Membership test: check if left is in right (array, tuple, dict, or string)
                    match right_val {
                        Value::Array(arr) => Ok(Value::Bool(arr.contains(&left_val))),
                        Value::Tuple(tup) => Ok(Value::Bool(tup.contains(&left_val))),
                        Value::Dict(dict) => {
                            let key = left_val.to_key_string();
                            Ok(Value::Bool(dict.contains_key(&key)))
                        }
                        Value::Str(s) => {
                            let needle = left_val.to_key_string();
                            Ok(Value::Bool(s.contains(&needle)))
                        }
                        _ => Err(CompileError::Semantic(
                            "'in' operator requires array, tuple, dict, or string".into(),
                        )),
                    }
                }
            }
        }
        Expr::Unary { op, operand } => {
            let val = evaluate_expr(operand, env, functions, classes, enums, impl_methods)?;

            // Check for unit type safety
            if let Value::Unit { value, suffix, family } = &val {
                match op {
                    UnaryOp::Neg => {
                        // Check if negation is allowed for this unit family
                        let unit_family = family.as_ref().map(|s| s.as_str()).unwrap_or(suffix.as_str());
                        match check_unit_unary_op(unit_family, *op) {
                            Ok(_result_family) => {
                                // Negation allowed - perform it on inner value
                                let inner_result = evaluate_unit_unary_inner(value, *op)?;
                                return Ok(Value::Unit {
                                    value: Box::new(inner_result),
                                    suffix: suffix.clone(),
                                    family: family.clone(),
                                });
                            }
                            Err(err) => {
                                return Err(CompileError::Semantic(err));
                            }
                        }
                    }
                    UnaryOp::Not | UnaryOp::BitNot => {
                        return Err(CompileError::Semantic(format!(
                            "cannot apply {:?} to unit value '{}'",
                            op, suffix
                        )));
                    }
                    UnaryOp::Ref => {
                        return Ok(Value::Borrow(BorrowValue::new(val)));
                    }
                    UnaryOp::RefMut => {
                        return Ok(Value::BorrowMut(BorrowMutValue::new(val)));
                    }
                    UnaryOp::Deref => {
                        return Ok(val.deref_pointer());
                    }
                }
            }

            match op {
                UnaryOp::Neg => Ok(Value::Int(-val.as_int()?)),
                UnaryOp::Not => Ok(Value::Bool(!val.truthy())),
                UnaryOp::BitNot => Ok(Value::Int(!val.as_int()?)),
                UnaryOp::Ref => Ok(Value::Borrow(BorrowValue::new(val))),
                UnaryOp::RefMut => Ok(Value::BorrowMut(BorrowMutValue::new(val))),
                UnaryOp::Deref => Ok(val.deref_pointer()),
            }
        }
        Expr::Lambda { params, body, move_mode } => {
            let names: Vec<String> = params
                .iter()
                .map(|LambdaParam { name, .. }| name.clone())
                .collect();
            // For move closures, we capture by value (clone the environment)
            // For regular closures, we share the environment reference
            // In the interpreter, both behave the same since we clone env anyway
            let captured_env = if move_mode.is_move() {
                // Move closure: capture a snapshot of current env
                env.clone()
            } else {
                env.clone()
            };
            Ok(Value::Lambda {
                params: names,
                body: body.clone(),
                env: captured_env,
            })
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            if evaluate_expr(condition, env, functions, classes, enums, impl_methods)?.truthy() {
                evaluate_expr(then_branch, env, functions, classes, enums, impl_methods)
            } else if let Some(else_b) = else_branch {
                evaluate_expr(else_b, env, functions, classes, enums, impl_methods)
            } else {
                Ok(Value::Nil)
            }
        }
        Expr::Match { subject, arms } => {
            let subject_val = evaluate_expr(subject, env, functions, classes, enums, impl_methods)?;

            // Check for strong enum - disallow wildcard/catch-all patterns
            if let Value::Enum { enum_name, .. } = &subject_val {
                if let Some(enum_def) = enums.get(enum_name) {
                    let is_strong = enum_def.attributes.iter().any(|attr| attr.name == ATTR_STRONG);
                    if is_strong {
                        for arm in arms {
                            if is_catch_all_pattern(&arm.pattern) {
                                return Err(CompileError::Semantic(format!(
                                    "strong enum '{}' does not allow wildcard or catch-all patterns in match",
                                    enum_name
                                )));
                            }
                        }
                    }
                }
            }

            for arm in arms {
                let mut arm_bindings = HashMap::new();
                if pattern_matches(&arm.pattern, &subject_val, &mut arm_bindings, enums)? {
                    if let Some(guard) = &arm.guard {
                        let mut guard_env = env.clone();
                        for (name, value) in &arm_bindings {
                            guard_env.insert(name.clone(), value.clone());
                        }
                        let guard_result = evaluate_expr(guard, &mut guard_env, functions, classes, enums, impl_methods)?;
                        if !guard_result.truthy() {
                            continue;
                        }
                    }
                    let mut arm_env = env.clone();
                    for (name, value) in arm_bindings {
                        arm_env.insert(name, value);
                    }
                    let mut result = Value::Nil;
                    for stmt in &arm.body.statements {
                        match exec_node(stmt, &mut arm_env, functions, classes, enums, impl_methods)? {
                            Control::Return(v) => return Ok(v),
                            Control::Break(_) => return Ok(Value::Nil),
                            Control::Continue => break,
                            Control::Next => {
                                if let Node::Expression(expr) = stmt {
                                    result = evaluate_expr(expr, &mut arm_env, functions, classes, enums, impl_methods)?;
                                }
                            }
                        }
                    }
                    return Ok(result);
                }
            }
            Err(CompileError::Semantic("match exhausted: no pattern matched".into()))
        }
        Expr::Call { callee, args } => {
            evaluate_call(callee, args, env, functions, classes, enums, impl_methods)
        }
        Expr::MethodCall {
            receiver,
            method,
            args,
        } => evaluate_method_call(
            receiver,
            method,
            args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        ),
        Expr::FieldAccess { receiver, field } => {
            // Support module-style access (lib.foo) by resolving directly to functions/classes
            if let Expr::Identifier(module_name) = receiver.as_ref() {
                if env.get(module_name).is_none() {
                    if let Some(func) = functions.get(field) {
                        return Ok(Value::Function {
                            name: field.clone(),
                            def: Box::new(func.clone()),
                            captured_env: Env::new(),
                        });
                    }
                    if classes.contains_key(field) {
                        return Ok(Value::Constructor {
                            class_name: field.clone(),
                        });
                    }
                }
            }

            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?
                .deref_pointer();
            match recv_val {
                Value::Object { ref fields, ref class, .. } => {
                    // First, try direct field access
                    if let Some(val) = fields.get(field) {
                        return Ok(val.clone());
                    }
                    // Auto-initializing internal fields: fields starting with '_' default to 0
                    if field.starts_with('_') {
                        return Ok(Value::Int(0));
                    }
                    // Auto-forwarding: try get_<field>() or is_<field>() methods
                    let getter_name = format!("get_{}", field);
                    let is_getter_name = format!("is_{}", field);

                    if let Some(class_def) = classes.get(class) {
                        // Try get_<field>
                        if let Some(method) = class_def.methods.iter().find(|m| m.name == getter_name) {
                            // Call the getter method with self
                            let self_val = Value::Object {
                                class: class.clone(),
                                fields: fields.clone(),
                            };
                            return exec_method_function(method, &[], &self_val, env, functions, classes, enums, impl_methods);
                        }
                        // Try is_<field>
                        if let Some(method) = class_def.methods.iter().find(|m| m.name == is_getter_name) {
                            let self_val = Value::Object {
                                class: class.clone(),
                                fields: fields.clone(),
                            };
                            return exec_method_function(method, &[], &self_val, env, functions, classes, enums, impl_methods);
                        }
                    }
                    Err(CompileError::Semantic(format!("unknown field {field}")))
                }
                Value::Constructor { ref class_name } => {
                    // Look up static method on class
                    if let Some(class_def) = classes.get(class_name) {
                        if let Some(method) = class_def.methods.iter().find(|m| &m.name == field) {
                            // Return as a function value for call
                            Ok(Value::Function {
                                name: method.name.clone(),
                                def: Box::new(method.clone()),
                                captured_env: Env::new(),
                            })
                        } else {
                            Err(CompileError::Semantic(format!("unknown method {field} on class {class_name}")))
                        }
                    } else {
                        Err(CompileError::Semantic(format!("unknown class {class_name}")))
                    }
                }
                // String property access (e.g., str.len, str.is_empty)
                Value::Str(ref s) => {
                    match field.as_str() {
                        "len" => Ok(Value::Int(s.len() as i64)),
                        "byte_len" => Ok(Value::Int(s.len() as i64)),
                        "char_count" => Ok(Value::Int(s.chars().count() as i64)),
                        "is_empty" => Ok(Value::Bool(s.is_empty())),
                        _ => Err(CompileError::Semantic(format!("unknown property '{field}' on String"))),
                    }
                }
                // Array property access (e.g., arr.len, arr.is_empty)
                Value::Array(ref arr) => {
                    match field.as_str() {
                        "len" => Ok(Value::Int(arr.len() as i64)),
                        "is_empty" => Ok(Value::Bool(arr.is_empty())),
                        _ => Err(CompileError::Semantic(format!("unknown property '{field}' on Array"))),
                    }
                }
                // Tuple property access (e.g., tup.len)
                Value::Tuple(ref tup) => {
                    match field.as_str() {
                        "len" => Ok(Value::Int(tup.len() as i64)),
                        _ => Err(CompileError::Semantic(format!("unknown property '{field}' on Tuple"))),
                    }
                }
                // Dict property access (e.g., dict.len, dict.is_empty)
                Value::Dict(ref map) => {
                    match field.as_str() {
                        "len" => Ok(Value::Int(map.len() as i64)),
                        "is_empty" => Ok(Value::Bool(map.is_empty())),
                        _ => Err(CompileError::Semantic(format!("unknown property '{field}' on Dict"))),
                    }
                }
                // Enum property access (Option/Result properties)
                Value::Enum { ref enum_name, ref variant, .. } => {
                    // Option properties: is_some, is_none
                    if enum_name == "Option" {
                        match field.as_str() {
                            "is_some" => Ok(Value::Bool(variant == "Some")),
                            "is_none" => Ok(Value::Bool(variant == "None")),
                            _ => Err(CompileError::Semantic(format!("unknown property '{field}' on Option"))),
                        }
                    }
                    // Result properties: is_ok, is_err
                    else if enum_name == "Result" {
                        match field.as_str() {
                            "is_ok" => Ok(Value::Bool(variant == "Ok")),
                            "is_err" => Ok(Value::Bool(variant == "Err")),
                            _ => Err(CompileError::Semantic(format!("unknown property '{field}' on Result"))),
                        }
                    }
                    else {
                        Err(CompileError::Semantic(format!("unknown property '{field}' on enum {enum_name}")))
                    }
                }
                _ => Err(CompileError::Semantic("field access on non-object".into())),
            }
        }
        Expr::StructInit { name, fields } => {
            let mut map = HashMap::new();
            for (fname, fexpr) in fields {
                let v = evaluate_expr(fexpr, env, functions, classes, enums, impl_methods)?;
                map.insert(fname.clone(), v);
            }
            Ok(Value::Object {
                class: name.clone(),
                fields: map,
            })
        }
        Expr::Path(segments) => {
            if segments.len() == 2 {
                let enum_name = &segments[0];
                let variant = &segments[1];
                if let Some(enum_def) = enums.get(enum_name) {
                    if enum_def.variants.iter().any(|v| &v.name == variant) {
                        Ok(Value::Enum {
                            enum_name: enum_name.clone(),
                            variant: variant.clone(),
                            payload: None,
                        })
                    } else {
                        Err(CompileError::Semantic(format!(
                            "unknown variant {variant} for enum {enum_name}"
                        )))
                    }
                } else if let Some(func) = functions.get(variant) {
                    Ok(Value::Function {
                        name: variant.clone(),
                        def: Box::new(func.clone()),
                        captured_env: Env::new(),
                    })
                } else if classes.contains_key(variant) {
                    Ok(Value::Constructor {
                        class_name: variant.clone(),
                    })
                } else {
                    Err(CompileError::Semantic(format!("unknown path: {:?}::{variant}", segments[0])))
                }
            } else {
                Err(CompileError::Semantic(format!(
                    "unsupported path: {:?}",
                    segments
                )))
            }
        }
        Expr::Dict(entries) => {
            let mut map = HashMap::new();
            for (k, v) in entries {
                // Handle dict spread: **expr
                if let Expr::DictSpread(inner) = k {
                    let spread_val =
                        evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
                    if let Value::Dict(spread_map) = spread_val {
                        for (sk, sv) in spread_map {
                            map.insert(sk, sv);
                        }
                    } else {
                        return Err(CompileError::Semantic(
                            "dict spread requires dict value".into(),
                        ));
                    }
                } else {
                    let key_val = evaluate_expr(k, env, functions, classes, enums, impl_methods)?;
                    let val = evaluate_expr(v, env, functions, classes, enums, impl_methods)?;
                    map.insert(key_val.to_key_string(), val);
                }
            }
            Ok(Value::Dict(map))
        }
        Expr::Range { start, end, bound } => {
            let start = start
                .as_ref()
                .map(|s| evaluate_expr(s, env, functions, classes, enums, impl_methods))
                .transpose()?
                .unwrap_or(Value::Int(0))
                .as_int()?;
            let end = end
                .as_ref()
                .map(|e| evaluate_expr(e, env, functions, classes, enums, impl_methods))
                .transpose()?
                .unwrap_or(Value::Int(0))
                .as_int()?;
            Ok(create_range_object(start, end, *bound))
        }
        Expr::Array(items) => {
            let mut arr = Vec::new();
            for item in items {
                // Handle spread operator: *expr
                if let Expr::Spread(inner) = item {
                    let spread_val =
                        evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
                    match spread_val {
                        Value::Array(spread_arr) => arr.extend(spread_arr),
                        Value::Tuple(tup) => arr.extend(tup),
                        _ => {
                            return Err(CompileError::Semantic(
                                "spread operator requires array or tuple".into(),
                            ))
                        }
                    }
                } else {
                    arr.push(evaluate_expr(
                        item,
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?);
                }
            }
            Ok(Value::Array(arr))
        }
        Expr::Tuple(items) => {
            let mut tup = Vec::new();
            for item in items {
                tup.push(evaluate_expr(
                    item,
                    env,
                    functions,
                    classes,
                    enums,
                    impl_methods,
                )?);
            }
            Ok(Value::Tuple(tup))
        }
        Expr::Index { receiver, index } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?
                .deref_pointer();
            let idx_val = evaluate_expr(index, env, functions, classes, enums, impl_methods)?;
            match recv_val {
                Value::Array(arr) => {
                    let raw_idx = idx_val.as_int()?;
                    let len = arr.len() as i64;
                    // Support negative indexing
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    arr.get(idx).cloned().ok_or_else(|| {
                        CompileError::Semantic(format!("array index out of bounds: {raw_idx}"))
                    })
                }
                Value::Tuple(tup) => {
                    let raw_idx = idx_val.as_int()?;
                    let len = tup.len() as i64;
                    // Support negative indexing
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    tup.get(idx).cloned().ok_or_else(|| {
                        CompileError::Semantic(format!("tuple index out of bounds: {raw_idx}"))
                    })
                }
                Value::Dict(map) => {
                    let key = idx_val.to_key_string();
                    map.get(&key)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("dict key not found: {key}")))
                }
                Value::Str(s) => {
                    let raw_idx = idx_val.as_int()?;
                    let len = s.chars().count() as i64;
                    // Support negative indexing
                    let idx = if raw_idx < 0 {
                        (len + raw_idx) as usize
                    } else {
                        raw_idx as usize
                    };
                    s.chars()
                        .nth(idx)
                        .map(|c| Value::Str(c.to_string()))
                        .ok_or_else(|| {
                            CompileError::Semantic(format!("string index out of bounds: {raw_idx}"))
                        })
                }
                Value::Object { fields, .. } => {
                    let key = idx_val.to_key_string();
                    fields
                        .get(&key)
                        .cloned()
                        .ok_or_else(|| CompileError::Semantic(format!("key not found: {key}")))
                }
                _ => Err(CompileError::Semantic(
                    "index access on non-indexable type".into(),
                )),
            }
        }
        // Tuple element access with literal index: tuple.0, tuple.1
        Expr::TupleIndex { receiver, index } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?
                .deref_pointer();
            match recv_val {
                Value::Tuple(tup) => {
                    tup.get(*index).cloned().ok_or_else(|| {
                        CompileError::Semantic(format!("tuple index out of bounds: {index}"))
                    })
                }
                _ => Err(CompileError::Semantic(
                    "tuple index access on non-tuple type".into(),
                )),
            }
        }
        Expr::ListComprehension {
            expr,
            pattern,
            iterable,
            condition,
        } => {
            let iter_val = evaluate_expr(iterable, env, functions, classes, enums, impl_methods)?;
            let envs = comprehension_iterate(
                &iter_val, pattern, condition, env, functions, classes, enums, impl_methods,
            )?;

            let mut result = Vec::new();
            for mut inner_env in envs {
                let val = evaluate_expr(expr, &mut inner_env, functions, classes, enums, impl_methods)?;
                result.push(val);
            }
            Ok(Value::Array(result))
        }
        Expr::DictComprehension {
            key,
            value,
            pattern,
            iterable,
            condition,
        } => {
            let iter_val = evaluate_expr(iterable, env, functions, classes, enums, impl_methods)?;
            let envs = comprehension_iterate(
                &iter_val, pattern, condition, env, functions, classes, enums, impl_methods,
            )?;

            let mut result = HashMap::new();
            for mut inner_env in envs {
                let k = evaluate_expr(key, &mut inner_env, functions, classes, enums, impl_methods)?;
                let v = evaluate_expr(value, &mut inner_env, functions, classes, enums, impl_methods)?;
                result.insert(k.to_key_string(), v);
            }
            Ok(Value::Dict(result))
        }
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => {
            let recv_val = evaluate_expr(receiver, env, functions, classes, enums, impl_methods)?
                .deref_pointer();
            let len = match &recv_val {
                Value::Array(arr) => arr.len() as i64,
                Value::Str(s) => s.len() as i64,
                Value::Tuple(t) => t.len() as i64,
                _ => return Err(CompileError::Semantic("slice on non-sliceable type".into())),
            };

            // Parse start, end, step with Python-style semantics
            let start_idx = if let Some(s) = start {
                let v = evaluate_expr(s, env, functions, classes, enums, impl_methods)?.as_int()?;
                normalize_index(v, len)
            } else {
                0
            };

            let end_idx = if let Some(e) = end {
                let v = evaluate_expr(e, env, functions, classes, enums, impl_methods)?.as_int()?;
                normalize_index(v, len)
            } else {
                len
            };

            let step_val = if let Some(st) = step {
                evaluate_expr(st, env, functions, classes, enums, impl_methods)?.as_int()?
            } else {
                1
            };

            if step_val == 0 {
                return Err(CompileError::Semantic("slice step cannot be zero".into()));
            }

            match recv_val {
                Value::Array(arr) => Ok(Value::Array(slice_collection(
                    &arr, start_idx, end_idx, step_val,
                ))),
                Value::Str(s) => {
                    let chars: Vec<char> = s.chars().collect();
                    let sliced = slice_collection(&chars, start_idx, end_idx, step_val);
                    Ok(Value::Str(sliced.into_iter().collect()))
                }
                Value::Tuple(tup) => Ok(Value::Tuple(slice_collection(
                    &tup, start_idx, end_idx, step_val,
                ))),
                _ => Err(CompileError::Semantic("slice on non-sliceable type".into())),
            }
        }
        Expr::Spread(inner) => {
            // Spread is handled by Array/Dict evaluation, but standalone should work too
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            Ok(val)
        }
        Expr::DictSpread(inner) => {
            // DictSpread is handled by Dict evaluation
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            Ok(val)
        }
        Expr::Spawn(inner) => Ok(spawn_actor_with_expr(
            inner,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        )),
        Expr::Await(inner) => {
            check_effect_violations("await")?;
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match val {
                Value::Future(f) => f.await_result().map_err(|e| CompileError::Semantic(e)),
                Value::Actor(handle) => {
                    handle.join().map_err(|e| CompileError::Semantic(e))?;
                    Ok(Value::Nil)
                }
                other => Ok(other),
            }
        }
        Expr::Yield(maybe_val) => {
            let yield_val = match maybe_val {
                Some(expr) => evaluate_expr(expr, env, functions, classes, enums, impl_methods)?,
                None => Value::Nil,
            };

            let added = GENERATOR_YIELDS.with(|cell| {
                if let Some(yields) = cell.borrow_mut().as_mut() {
                    yields.push(yield_val.clone());
                    true
                } else {
                    false
                }
            });

            if !added {
                return Err(CompileError::Semantic(
                    "yield called outside of generator".into(),
                ));
            }

            Ok(Value::Nil)
        }
        Expr::FunctionalUpdate {
            target,
            method,
            args,
        } => {
            let method_call = Expr::MethodCall {
                receiver: target.clone(),
                method: method.clone(),
                args: args.clone(),
            };
            evaluate_expr(&method_call, env, functions, classes, enums, impl_methods)
        }
        Expr::MacroInvocation {
            name,
            args: macro_args,
        } => evaluate_macro_invocation(
            name,
            macro_args,
            env,
            functions,
            classes,
            enums,
            impl_methods,
        ),
        Expr::Try(inner) => {
            // Try operator: expr? - unwrap Ok or propagate Err
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            match val {
                Value::Enum {
                    ref enum_name,
                    ref variant,
                    ref payload,
                } if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Result) => {
                    match ResultVariant::from_name(variant) {
                        Some(ResultVariant::Ok) => {
                            if let Some(inner_val) = payload {
                                Ok(inner_val.as_ref().clone())
                            } else {
                                Ok(Value::Nil)
                            }
                        }
                        Some(ResultVariant::Err) => {
                            // Return the Err as a TryError that should be propagated
                            Err(CompileError::TryError(val))
                        }
                        None => Err(CompileError::Semantic(format!(
                            "invalid Result variant: {}",
                            variant
                        ))),
                    }
                }
                Value::Enum {
                    ref enum_name,
                    ref variant,
                    ref payload,
                } if SpecialEnumType::from_name(enum_name) == Some(SpecialEnumType::Option) => {
                    match OptionVariant::from_name(variant) {
                        Some(OptionVariant::Some) => {
                            if let Some(inner_val) = payload {
                                Ok(inner_val.as_ref().clone())
                            } else {
                                Ok(Value::Nil)
                            }
                        }
                        Some(OptionVariant::None) => {
                            // Return None as a TryError
                            Err(CompileError::TryError(val))
                        }
                        None => Err(CompileError::Semantic(format!(
                            "invalid Option variant: {}",
                            variant
                        ))),
                    }
                }
                _ => Err(CompileError::Semantic(
                    "? operator requires Result or Option type".into(),
                )),
            }
        }
        // Contract expressions - not supported in interpreter yet
        Expr::ContractResult => Err(CompileError::Semantic(
            "contract 'result' keyword can only be used in contract blocks".into(),
        )),
        Expr::ContractOld(_) => Err(CompileError::Semantic(
            "contract old() expression can only be used in ensures blocks".into(),
        )),
        // DoBlock - a block of statements used as a closure (BDD DSL colon-blocks)
        Expr::DoBlock(nodes) => {
            Ok(Value::BlockClosure {
                nodes: nodes.clone(),
                env: env.clone(),
            })
        }
        #[allow(unreachable_patterns)]
        _ => Err(CompileError::Semantic(format!(
            "unsupported expression type: {:?}",
            expr
        ))),
    }
}
