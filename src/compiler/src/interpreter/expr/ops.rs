use std::collections::HashMap;

use simple_parser::ast::{BinOp, Expr, PointerKind, UnaryOp};

use super::casting::cast_value;
use super::evaluate_expr;
use super::units::{evaluate_unit_binary_inner, evaluate_unit_unary_inner};
use crate::error::{codes, CompileError, ErrorContext};
use crate::value::{
    BorrowMutValue, BorrowValue, ManualHandleValue, ManualSharedValue, ManualUniqueValue, ManualWeakValue, Value,
};

use super::super::{await_value, check_unit_binary_op, check_unit_unary_op, ClassDef, Enums, Env, FunctionDef, ImplMethods};
use super::super::core_types::get_identifier_name;
use super::super::interpreter_state::{CONST_NAMES, IMMUTABLE_VARS};

/// Check if a variable name refers to an immutable binding
fn is_variable_immutable(name: &str) -> bool {
    CONST_NAMES.with(|cell| cell.borrow().contains(name)) || IMMUTABLE_VARS.with(|cell| cell.borrow().contains(name))
}

/// Check if a value is a pointer type (can be dereferenced)
fn is_pointer_type(val: &Value) -> bool {
    matches!(
        val,
        Value::Unique(_)
            | Value::Shared(_)
            | Value::Weak(_)
            | Value::Handle(_)
            | Value::Borrow(_)
            | Value::BorrowMut(_)
    )
}

pub(super) fn eval_op_expr(
    expr: &Expr,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    match expr {
        Expr::New { kind, expr } => {
            let inner = evaluate_expr(expr, env, functions, classes, enums, impl_methods)?;
            let result = match kind {
                PointerKind::Unique => Ok(Value::Unique(ManualUniqueValue::new(inner))),
                PointerKind::Shared => Ok(Value::Shared(ManualSharedValue::new(inner))),
                PointerKind::Weak => {
                    if let Value::Shared(shared) = inner {
                        Ok(Value::Weak(ManualWeakValue::new_from_shared(&shared)))
                    } else {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_OPERATION)
                            .with_help("weak references can only be created from shared pointers");
                        Err(CompileError::semantic_with_context(
                            "invalid operation: cannot create weak reference from non-shared pointer",
                            ctx,
                        ))
                    }
                }
                PointerKind::Handle => Ok(Value::Handle(ManualHandleValue::new(inner))),
                PointerKind::Borrow => Ok(Value::Borrow(BorrowValue::new(inner))),
                PointerKind::BorrowMut => Ok(Value::BorrowMut(BorrowMutValue::new(inner))),
                // Raw pointers for FFI - treat as shared pointers at runtime
                PointerKind::RawConst => Ok(Value::Shared(ManualSharedValue::new(inner))),
                PointerKind::RawMut => Ok(Value::Shared(ManualSharedValue::new(inner))),
            };
            Ok(Some(result?))
        }
        Expr::Binary { op, left, right } => {
            // Handle suspension boolean operators specially (lazy evaluation with await)
            // and~ : evaluate left, if truthy then await right and return logical AND
            // or~  : evaluate left, if truthy return true, else await right and return result
            match op {
                BinOp::AndSuspend => {
                    let left_val = evaluate_expr(left, env, functions, classes, enums, impl_methods)?;
                    if !left_val.truthy() {
                        // Short-circuit: left is falsy, don't evaluate right
                        return Ok(Some(Value::Bool(false)));
                    }
                    // Left is truthy, await right and return logical AND
                    let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)?;
                    let awaited_right = await_value(right_val)?;
                    return Ok(Some(Value::Bool(awaited_right.truthy())));
                }
                BinOp::OrSuspend => {
                    let left_val = evaluate_expr(left, env, functions, classes, enums, impl_methods)?;
                    if left_val.truthy() {
                        // Short-circuit: left is truthy, don't evaluate right
                        return Ok(Some(Value::Bool(true)));
                    }
                    // Left is falsy, await right and return its truthiness
                    let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)?;
                    let awaited_right = await_value(right_val)?;
                    return Ok(Some(Value::Bool(awaited_right.truthy())));
                }
                _ => {} // Fall through to normal handling
            }

            let left_val = evaluate_expr(left, env, functions, classes, enums, impl_methods)?;
            let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)?;

            // Check for unit arithmetic type safety
            match (&left_val, &right_val) {
                (
                    Value::Unit {
                        value: lv,
                        suffix: ls,
                        family: lf,
                    },
                    Value::Unit {
                        value: rv,
                        suffix: rs,
                        family: rf,
                    },
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
                            return Ok(Some(Value::Unit {
                                value: Box::new(result_val),
                                suffix: result_suffix,
                                family: result_family.or_else(|| lf.clone()),
                            }));
                        }
                        Err(err) => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_OPERATION)
                                .with_help("check that the operation is valid for the unit types");
                            return Err(CompileError::semantic_with_context(
                                format!("invalid operation: {}", err),
                                ctx,
                            ));
                        }
                    }
                }
                // Mixed unit/non-unit operations: allow scaling (mul/div)
                (Value::Unit { value, suffix, family }, other) | (other, Value::Unit { value, suffix, family })
                    if matches!(op, BinOp::Mul | BinOp::Div) =>
                {
                    // Scaling: unit * scalar or scalar * unit (or division)
                    let inner_result = evaluate_unit_binary_inner(value, other, *op)?;
                    return Ok(Some(Value::Unit {
                        value: Box::new(inner_result),
                        suffix: suffix.clone(),
                        family: family.clone(),
                    }));
                }
                // Mixed unit/non-unit for non-scaling ops is an error
                (Value::Unit { suffix: ls, .. }, _) => {
                    if !matches!(op, BinOp::Eq | BinOp::NotEq) {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_OPERATION)
                            .with_help(format!(
                                "unit '{}' operations require both operands to be compatible units or scalar values",
                                ls
                            ));
                        return Err(CompileError::semantic_with_context(
                            format!(
                                "invalid operation: cannot apply {:?} between unit '{}' and non-unit value",
                                op, ls
                            ),
                            ctx,
                        ));
                    }
                    // Fall through for equality comparison
                }
                (_, Value::Unit { suffix: rs, .. }) => {
                    if !matches!(op, BinOp::Eq | BinOp::NotEq) {
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_OPERATION)
                            .with_help(format!(
                                "unit '{}' operations require both operands to be compatible units or scalar values",
                                rs
                            ));
                        return Err(CompileError::semantic_with_context(
                            format!(
                                "invalid operation: cannot apply {:?} between non-unit value and unit '{}'",
                                op, rs
                            ),
                            ctx,
                        ));
                    }
                    // Fall through for equality comparison
                }
                _ => {} // Neither is a unit - fall through to normal handling
            }

            // Standard binary operation handling (for non-unit operations)
            // Helper to determine if we should use float arithmetic
            let use_float = matches!(&left_val, Value::Float(_)) || matches!(&right_val, Value::Float(_));

            let result = match op {
                BinOp::Add => match (&left_val, &right_val) {
                    (Value::Str(a), Value::Str(b)) => Ok(Value::Str(format!("{a}{b}"))),
                    (Value::Str(a), b) => Ok(Value::Str(format!("{a}{}", b.to_display_string()))),
                    (a, Value::Str(b)) => Ok(Value::Str(format!("{}{}", a.to_display_string(), b))),
                    // Array concatenation: [a, b] + [c, d] => [a, b, c, d]
                    (Value::Array(a), Value::Array(b)) => {
                        let mut result = a.clone();
                        result.extend(b.iter().cloned());
                        Ok(Value::Array(result))
                    }
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
                    // String repetition: "a" * 3 -> "aaa" or 3 * "a" -> "aaa"
                    match (&left_val, &right_val) {
                        (Value::Str(s), Value::Int(n)) => {
                            if *n <= 0 {
                                Ok(Value::Str(String::new()))
                            } else {
                                Ok(Value::Str(s.repeat(*n as usize)))
                            }
                        }
                        (Value::Int(n), Value::Str(s)) => {
                            if *n <= 0 {
                                Ok(Value::Str(String::new()))
                            } else {
                                Ok(Value::Str(s.repeat(*n as usize)))
                            }
                        }
                        _ if use_float => Ok(Value::Float(left_val.as_float()? * right_val.as_float()?)),
                        _ => Ok(Value::Int(left_val.as_int()? * right_val.as_int()?)),
                    }
                }
                BinOp::Div => {
                    if use_float {
                        let r = right_val.as_float()?;
                        if r == 0.0 {
                            // E3001 - Division By Zero
                            let ctx = ErrorContext::new()
                                .with_code(codes::DIVISION_BY_ZERO)
                                .with_help("cannot divide by zero")
                                .with_note("check that the divisor is not zero before division");
                            Err(CompileError::semantic_with_context("division by zero".to_string(), ctx))
                        } else {
                            Ok(Value::Float(left_val.as_float()? / r))
                        }
                    } else {
                        let r = right_val.as_int()?;
                        if r == 0 {
                            // E3001 - Division By Zero
                            let ctx = ErrorContext::new()
                                .with_code(codes::DIVISION_BY_ZERO)
                                .with_help("cannot divide by zero")
                                .with_note("check that the divisor is not zero before division");
                            Err(CompileError::semantic_with_context("division by zero".to_string(), ctx))
                        } else {
                            Ok(Value::Int(left_val.as_int()? / r))
                        }
                    }
                }
                BinOp::Mod => {
                    if use_float {
                        let r = right_val.as_float()?;
                        if r == 0.0 {
                            // E3001 - Division By Zero (includes modulo)
                            let ctx = ErrorContext::new()
                                .with_code(codes::DIVISION_BY_ZERO)
                                .with_help("cannot perform modulo by zero")
                                .with_note("check that the divisor is not zero before modulo operation");
                            Err(CompileError::semantic_with_context("modulo by zero".to_string(), ctx))
                        } else {
                            Ok(Value::Float(left_val.as_float()? % r))
                        }
                    } else {
                        let r = right_val.as_int()?;
                        if r == 0 {
                            // E3001 - Division By Zero (includes modulo)
                            let ctx = ErrorContext::new()
                                .with_code(codes::DIVISION_BY_ZERO)
                                .with_help("cannot perform modulo by zero")
                                .with_note("check that the divisor is not zero before modulo operation");
                            Err(CompileError::semantic_with_context("modulo by zero".to_string(), ctx))
                        } else {
                            Ok(Value::Int(left_val.as_int()? % r))
                        }
                    }
                }
                BinOp::Eq => Ok(Value::Bool(left_val == right_val)),
                BinOp::NotEq => Ok(Value::Bool(left_val != right_val)),
                BinOp::Lt => match (&left_val, &right_val) {
                    (Value::Str(a), Value::Str(b)) => Ok(Value::Bool(a < b)),
                    _ if use_float => Ok(Value::Bool(left_val.as_float()? < right_val.as_float()?)),
                    _ => Ok(Value::Bool(left_val.as_int()? < right_val.as_int()?)),
                },
                BinOp::Gt => match (&left_val, &right_val) {
                    (Value::Str(a), Value::Str(b)) => Ok(Value::Bool(a > b)),
                    _ if use_float => Ok(Value::Bool(left_val.as_float()? > right_val.as_float()?)),
                    _ => Ok(Value::Bool(left_val.as_int()? > right_val.as_int()?)),
                },
                BinOp::LtEq => match (&left_val, &right_val) {
                    (Value::Str(a), Value::Str(b)) => Ok(Value::Bool(a <= b)),
                    _ if use_float => Ok(Value::Bool(left_val.as_float()? <= right_val.as_float()?)),
                    _ => Ok(Value::Bool(left_val.as_int()? <= right_val.as_int()?)),
                },
                BinOp::GtEq => match (&left_val, &right_val) {
                    (Value::Str(a), Value::Str(b)) => Ok(Value::Bool(a >= b)),
                    _ if use_float => Ok(Value::Bool(left_val.as_float()? >= right_val.as_float()?)),
                    _ => Ok(Value::Bool(left_val.as_int()? >= right_val.as_int()?)),
                },
                BinOp::Is => Ok(Value::Bool(left_val == right_val)),
                BinOp::And | BinOp::AndSuspend => Ok(Value::Bool(left_val.truthy() && right_val.truthy())),
                BinOp::Or | BinOp::OrSuspend => Ok(Value::Bool(left_val.truthy() || right_val.truthy())),
                BinOp::Pow => {
                    if use_float {
                        Ok(Value::Float(left_val.as_float()?.powf(right_val.as_float()?)))
                    } else {
                        let base = left_val.as_int()?;
                        let exp = right_val.as_int()?;
                        if exp < 0 {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_OPERATION)
                                .with_help("use float exponentiation for negative exponents");
                            Err(CompileError::semantic_with_context(
                                "invalid operation: negative exponent not supported for integers",
                                ctx,
                            ))
                        } else {
                            Ok(Value::Int(base.pow(exp as u32)))
                        }
                    }
                }
                BinOp::FloorDiv => {
                    let r = right_val.as_int()?;
                    if r == 0 {
                        // E3001 - Division By Zero
                        let ctx = ErrorContext::new()
                            .with_code(codes::DIVISION_BY_ZERO)
                            .with_help("cannot perform floor division by zero")
                            .with_note("check that the divisor is not zero before division");
                        Err(CompileError::semantic_with_context(
                            "floor division by zero".to_string(),
                            ctx,
                        ))
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
                        _ => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::TYPE_MISMATCH)
                                .with_help("'in' operator requires array, tuple, dict, or string");
                            Err(CompileError::semantic_with_context(
                                format!(
                                    "'in' operator requires array, tuple, dict, or string; got {}",
                                    right_val.type_name()
                                ),
                                ctx,
                            ))
                        }
                    }
                }
                BinOp::MatMul => {
                    // Matrix multiplication (@) - for now, treat as element-wise multiply for numbers
                    // or defer to a matrix library for actual matrix operations
                    if use_float {
                        Ok(Value::Float(left_val.as_float()? * right_val.as_float()?))
                    } else {
                        Ok(Value::Int(left_val.as_int()? * right_val.as_int()?))
                    }
                }
            };

            Ok(Some(result?))
        }
        Expr::Unary { op, operand } => {
            // E1053 - Cannot Borrow Immutable (check before evaluating operand)
            if matches!(op, UnaryOp::RefMut) {
                if let Some(var_name) = get_identifier_name(operand) {
                    if is_variable_immutable(var_name) {
                        let ctx = ErrorContext::new()
                            .with_code(codes::CANNOT_BORROW_IMMUTABLE)
                            .with_help("cannot take a mutable borrow of an immutable variable")
                            .with_note("consider declaring the variable as mutable with `let mut` or `var`");
                        return Err(CompileError::semantic_with_context(
                            format!("cannot borrow `{}` as mutable because it is immutable", var_name),
                            ctx,
                        ));
                    }
                }
            }

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
                                return Ok(Some(Value::Unit {
                                    value: Box::new(inner_result),
                                    suffix: suffix.clone(),
                                    family: family.clone(),
                                }));
                            }
                            Err(err) => {
                                let ctx = ErrorContext::new()
                                    .with_code(codes::INVALID_OPERATION)
                                    .with_help("check that this unary operation is supported for this unit type");
                                return Err(CompileError::semantic_with_context(
                                    format!("invalid operation: {}", err),
                                    ctx,
                                ));
                            }
                        }
                    }
                    UnaryOp::Not | UnaryOp::BitNot => {
                        // E1041 - Invalid Unary Op
                        let op_name = match op {
                            UnaryOp::Not => "!",
                            UnaryOp::BitNot => "~",
                            _ => "operator",
                        };
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_UNARY_OP)
                            .with_help(format!("operator `{}` cannot be applied to unit values", op_name));

                        return Err(CompileError::semantic_with_context(
                            format!("cannot apply operator `{}` to type `Unit<{}>`", op_name, suffix),
                            ctx,
                        ));
                    }
                    UnaryOp::Ref => {
                        return Ok(Some(Value::Borrow(BorrowValue::new(val))));
                    }
                    UnaryOp::RefMut => {
                        return Ok(Some(Value::BorrowMut(BorrowMutValue::new(val))));
                    }
                    UnaryOp::Deref => {
                        // E1054 - Invalid Dereference
                        if !is_pointer_type(&val) {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_DEREFERENCE)
                                .with_help("dereference operator (*) can only be applied to pointer types")
                                .with_note("pointer types include: unique, shared, weak, handle, borrow references");
                            return Err(CompileError::semantic_with_context(
                                format!("cannot dereference value of type `{}`", val.type_name()),
                                ctx,
                            ));
                        }
                        return Ok(Some(val.deref_pointer()));
                    }
                    UnaryOp::ChannelRecv => {
                        // E1041 - Invalid Unary Op
                        let ctx = ErrorContext::new()
                            .with_code(codes::INVALID_UNARY_OP)
                            .with_help("channel receive operator cannot be applied to unit values");

                        return Err(CompileError::semantic_with_context(
                            format!("cannot apply operator `<-` to type `Unit<{}>`", suffix),
                            ctx,
                        ));
                    }
                    UnaryOp::Move => {
                        // Move is a semantic marker for ownership transfer
                        // For unit types, just return the value unchanged
                        return Ok(Some(val));
                    }
                }
            }

            // E1054 - Invalid Dereference (check for non-unit types)
            if matches!(op, UnaryOp::Deref) && !is_pointer_type(&val) {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_DEREFERENCE)
                    .with_help("dereference operator (*) can only be applied to pointer types")
                    .with_note("pointer types include: unique, shared, weak, handle, borrow references");
                return Err(CompileError::semantic_with_context(
                    format!("cannot dereference value of type `{}`", val.type_name()),
                    ctx,
                ));
            }

            let result = match op {
                UnaryOp::Neg => {
                    // Preserve float type for negation
                    if matches!(val, Value::Float(_)) {
                        Value::Float(-val.as_float()?)
                    } else {
                        Value::Int(-val.as_int()?)
                    }
                }
                UnaryOp::Not => Value::Bool(!val.truthy()),
                UnaryOp::BitNot => Value::Int(!val.as_int()?),
                UnaryOp::Ref => Value::Borrow(BorrowValue::new(val)),
                UnaryOp::RefMut => Value::BorrowMut(BorrowMutValue::new(val)),
                UnaryOp::Deref => val.deref_pointer(),
                UnaryOp::ChannelRecv => {
                    // Channel receive: block until value is available
                    match val {
                        Value::Channel(channel) => channel.recv().map_err(|e| {
                            // E1203 - Channel Closed
                            let ctx = ErrorContext::new()
                                .with_code(codes::CHANNEL_CLOSED)
                                .with_help("check that the channel sender has not been dropped")
                                .with_note(format!("channel error: {}", e));
                            CompileError::semantic_with_context("channel closed or disconnected".to_string(), ctx)
                        })?,
                        _ => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::INVALID_OPERATION)
                                .with_help("channel receive operator (<-) can only be used on channel values");
                            return Err(CompileError::semantic_with_context(
                                format!(
                                    "invalid operation: cannot receive from non-channel value of type `{}`",
                                    val.type_name()
                                ),
                                ctx,
                            ));
                        }
                    }
                }
                UnaryOp::Move => {
                    // Move is a semantic marker for ownership transfer
                    // Just return the value unchanged - ownership tracking is compile-time only
                    val
                }
            };
            Ok(Some(result))
        }
        Expr::Cast {
            expr: inner,
            target_type,
        } => {
            let val = evaluate_expr(inner, env, functions, classes, enums, impl_methods)?;
            Ok(Some(cast_value(val, target_type)?))
        }
        _ => Ok(None),
    }
}
