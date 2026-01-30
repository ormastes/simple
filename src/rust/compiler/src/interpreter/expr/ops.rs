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
use super::super::coverage_helpers::record_condition_coverage;

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
                    let left_result = left_val.truthy();

                    // COVERAGE: Record left condition of &&~
                    record_condition_coverage("<source>", 0, 0, 0, left_result);

                    if !left_result {
                        // Short-circuit: left is falsy, don't evaluate right
                        // COVERAGE: Record that right side wasn't evaluated (false for completeness)
                        record_condition_coverage("<source>", 0, 0, 1, false);
                        return Ok(Some(Value::Bool(false)));
                    }
                    // Left is truthy, await right and return logical AND
                    let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)?;
                    let awaited_right = await_value(right_val)?;
                    let right_result = awaited_right.truthy();

                    // COVERAGE: Record right condition of &&~
                    record_condition_coverage("<source>", 0, 0, 1, right_result);

                    return Ok(Some(Value::Bool(right_result)));
                }
                BinOp::OrSuspend => {
                    let left_val = evaluate_expr(left, env, functions, classes, enums, impl_methods)?;
                    let left_result = left_val.truthy();

                    // COVERAGE: Record left condition of ||~
                    record_condition_coverage("<source>", 0, 1, 0, left_result);

                    if left_result {
                        // Short-circuit: left is truthy, don't evaluate right
                        // COVERAGE: Record that right side wasn't evaluated (true for completeness)
                        record_condition_coverage("<source>", 0, 1, 1, true);
                        return Ok(Some(Value::Bool(true)));
                    }
                    // Left is falsy, await right and return its truthiness
                    let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)?;
                    let awaited_right = await_value(right_val)?;
                    let right_result = awaited_right.truthy();

                    // COVERAGE: Record right condition of ||~
                    record_condition_coverage("<source>", 0, 1, 1, right_result);

                    return Ok(Some(Value::Bool(right_result)));
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
                BinOp::And | BinOp::AndSuspend => {
                    let left_result = left_val.truthy();
                    let right_result = right_val.truthy();
                    let combined = left_result && right_result;

                    // COVERAGE: Record condition coverage for && operator
                    record_condition_coverage("<source>", 0, 0, 0, left_result);
                    record_condition_coverage("<source>", 0, 0, 1, right_result);

                    Ok(Value::Bool(combined))
                }
                BinOp::Or | BinOp::OrSuspend => {
                    let left_result = left_val.truthy();
                    let right_result = right_val.truthy();
                    let combined = left_result || right_result;

                    // COVERAGE: Record condition coverage for || operator
                    record_condition_coverage("<source>", 0, 1, 0, left_result);
                    record_condition_coverage("<source>", 0, 1, 1, right_result);

                    Ok(Value::Bool(combined))
                }
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
                BinOp::BitAnd => Ok(Value::Int(left_val.as_int()? & right_val.as_int()?)),
                BinOp::BitOr => Ok(Value::Int(left_val.as_int()? | right_val.as_int()?)),
                BinOp::BitXor => Ok(Value::Int(left_val.as_int()? ^ right_val.as_int()?)),
                BinOp::ShiftLeft => Ok(Value::Int(left_val.as_int()? << right_val.as_int()?)),
                BinOp::ShiftRight => Ok(Value::Int(left_val.as_int()? >> right_val.as_int()?)),
                BinOp::In | BinOp::NotIn => {
                    // Membership test: check if left is in right (array, tuple, dict, or string)
                    let negate = matches!(op, BinOp::NotIn);
                    let result = match right_val {
                        Value::Array(arr) => Ok(Value::Bool(arr.contains(&left_val) ^ negate)),
                        Value::Tuple(tup) => Ok(Value::Bool(tup.contains(&left_val) ^ negate)),
                        Value::Dict(dict) => {
                            let key = left_val.to_key_string();
                            Ok(Value::Bool(dict.contains_key(&key) ^ negate))
                        }
                        Value::Str(s) => {
                            let needle = left_val.to_key_string();
                            Ok(Value::Bool(s.contains(&needle) ^ negate))
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
                    };
                    result
                }
                BinOp::MatMul => {
                    // Matrix multiplication (@) - Simple Math #1930-#1939
                    match (&left_val, &right_val) {
                        // Scalar @ Scalar - backward compatibility
                        (Value::Int(a), Value::Int(b)) => Ok(Value::Int(a * b)),
                        (Value::Float(a), Value::Float(b)) => Ok(Value::Float(a * b)),
                        (Value::Int(a), Value::Float(b)) => Ok(Value::Float(*a as f64 * b)),
                        (Value::Float(a), Value::Int(b)) => Ok(Value::Float(a * *b as f64)),

                        // Array @ Array - proper matrix multiplication
                        (Value::Array(a), Value::Array(b)) => {
                            if a.is_empty() || b.is_empty() {
                                let ctx = ErrorContext::new()
                                    .with_code(codes::INVALID_OPERATION)
                                    .with_help("matrix multiplication requires non-empty arrays");
                                return Err(CompileError::semantic_with_context(
                                    "matrix multiplication requires non-empty arrays",
                                    ctx,
                                ));
                            }

                            let is_a_2d = matches!(a.get(0), Some(Value::Array(_)));
                            let is_b_2d = matches!(b.get(0), Some(Value::Array(_)));

                            match (is_a_2d, is_b_2d) {
                                (false, false) => matmul_dot_product_1d(a, b),
                                (true, true) => matmul_matrix_multiply_2d(a, b),
                                (true, false) => matmul_matrix_vector(a, b),
                                (false, true) => matmul_vector_matrix(a, b),
                            }
                        }

                        _ => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::TYPE_MISMATCH)
                                .with_help("matrix multiplication requires arrays or scalars");
                            Err(CompileError::semantic_with_context(
                                format!(
                                    "@ operator requires numeric or array types, got {} @ {}",
                                    left_val.type_name(),
                                    right_val.type_name()
                                ),
                                ctx,
                            ))
                        }
                    }
                }
                BinOp::PipeForward => {
                    // Pipe forward: left |> right means right(left)
                    // right should be a function, left is the argument
                    match right_val {
                        Value::Function { def, captured_env, .. } => {
                            // Call the function with left_val as argument
                            let mut captured_env_clone = captured_env.clone();
                            let args = [left_val];
                            super::super::exec_function_with_values(
                                &def,
                                &args,
                                &mut captured_env_clone,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            )
                        }
                        _ => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::TYPE_MISMATCH)
                                .with_help("pipe forward operator |> requires a function on the right side");
                            Err(CompileError::semantic_with_context(
                                format!("cannot pipe to non-function: {}", right_val.type_name()),
                                ctx,
                            ))
                        }
                    }
                }
                BinOp::Parallel => {
                    // Parallel execution: f // g
                    // For now, execute sequentially (true parallelism requires async runtime)
                    // Returns array of results from concurrent execution
                    match (&left_val, &right_val) {
                        (Value::Function { .. }, Value::Function { .. }) => {
                            // Execute both functions (sequentially for now)
                            // TODO: Integrate with async runtime for true parallelism
                            let mut results = Vec::new();

                            // Execute left function
                            if let Value::Function { def, captured_env, .. } = left_val {
                                let mut captured_env_clone = captured_env.clone();
                                let left_result = super::super::exec_function_with_values(
                                    &def,
                                    &[],
                                    &mut captured_env_clone,
                                    functions,
                                    classes,
                                    enums,
                                    impl_methods,
                                )?;
                                results.push(left_result);
                            }

                            // Execute right function
                            if let Value::Function { def, captured_env, .. } = right_val {
                                let mut captured_env_clone = captured_env.clone();
                                let right_result = super::super::exec_function_with_values(
                                    &def,
                                    &[],
                                    &mut captured_env_clone,
                                    functions,
                                    classes,
                                    enums,
                                    impl_methods,
                                )?;
                                results.push(right_result);
                            }

                            Ok(Value::Array(results))
                        }
                        _ => {
                            let ctx = ErrorContext::new()
                                .with_code(codes::TYPE_MISMATCH)
                                .with_help("// operator requires function operands for parallel execution");
                            Err(CompileError::semantic_with_context(
                                format!(
                                    "// operator requires functions, got {} // {}",
                                    left_val.type_name(),
                                    right_val.type_name()
                                ),
                                ctx,
                            ))
                        }
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

//==============================================================================
// Matrix Multiplication Helper Functions (Simple Math #1930-#1939)
//==============================================================================

/// Compute dot product of two 1D arrays
fn matmul_dot_product_1d(a: &[Value], b: &[Value]) -> Result<Value, CompileError> {
    if a.len() != b.len() {
        let ctx = ErrorContext::new()
            .with_code(codes::INVALID_OPERATION)
            .with_help(format!(
                "dot product requires equal length arrays: {} != {}",
                a.len(),
                b.len()
            ));
        return Err(CompileError::semantic_with_context(
            format!("dimension mismatch for dot product: {} != {}", a.len(), b.len()),
            ctx,
        ));
    }

    let mut sum = Value::Int(0);
    let mut is_float = false;

    for (ai, bi) in a.iter().zip(b.iter()) {
        // Check if we need float mode
        if matches!(ai, Value::Float(_)) || matches!(bi, Value::Float(_)) {
            is_float = true;
        }

        let prod = match (ai, bi) {
            (Value::Int(x), Value::Int(y)) => Value::Int(x * y),
            (Value::Float(x), Value::Float(y)) => Value::Float(x * y),
            (Value::Int(x), Value::Float(y)) => Value::Float(*x as f64 * y),
            (Value::Float(x), Value::Int(y)) => Value::Float(x * *y as f64),
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help("dot product requires numeric array elements");
                return Err(CompileError::semantic_with_context(
                    format!("cannot multiply {} and {}", ai.type_name(), bi.type_name()),
                    ctx,
                ));
            }
        };

        sum = match (sum, prod) {
            (Value::Int(s), Value::Int(p)) => Value::Int(s + p),
            (Value::Float(s), Value::Float(p)) => Value::Float(s + p),
            (Value::Int(s), Value::Float(p)) => Value::Float(s as f64 + p),
            (Value::Float(s), Value::Int(p)) => Value::Float(s + p as f64),
            _ => unreachable!(),
        };
    }

    // Convert to float if needed
    if is_float && matches!(sum, Value::Int(_)) {
        sum = Value::Float(sum.as_int()? as f64);
    }

    Ok(sum)
}

/// Multiply two 2D matrices
fn matmul_matrix_multiply_2d(a: &[Value], b: &[Value]) -> Result<Value, CompileError> {
    // Extract dimensions
    let m = a.len();
    let n = match &a[0] {
        Value::Array(row) => row.len(),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("matrix multiplication requires 2D arrays (array of arrays)");
            return Err(CompileError::semantic_with_context(
                "first operand is not a 2D matrix",
                ctx,
            ));
        }
    };

    let p = b.len();
    let q = match &b[0] {
        Value::Array(row) => row.len(),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("matrix multiplication requires 2D arrays (array of arrays)");
            return Err(CompileError::semantic_with_context(
                "second operand is not a 2D matrix",
                ctx,
            ));
        }
    };

    if n != p {
        let ctx = ErrorContext::new()
            .with_code(codes::INVALID_OPERATION)
            .with_help("inner dimensions must match: A(m,n) @ B(n,q) = C(m,q)");
        return Err(CompileError::semantic_with_context(
            format!("incompatible matrix dimensions: ({}, {}) @ ({}, {})", m, n, p, q),
            ctx,
        ));
    }

    let mut result = Vec::with_capacity(m);
    for i in 0..m {
        let a_row = match &a[i] {
            Value::Array(row) => row,
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help("matrix must have uniform rows");
                return Err(CompileError::semantic_with_context(
                    "matrix row is not an array",
                    ctx,
                ));
            }
        };
        let mut row = Vec::with_capacity(q);

        for j in 0..q {
            let mut sum = Value::Int(0);
            let mut is_float = false;

            for k in 0..n {
                let a_ik = &a_row[k];
                let b_row = match &b[k] {
                    Value::Array(row) => row,
                    _ => {
                        let ctx = ErrorContext::new()
                            .with_code(codes::TYPE_MISMATCH)
                            .with_help("matrix must have uniform rows");
                        return Err(CompileError::semantic_with_context(
                            "matrix row is not an array",
                            ctx,
                        ));
                    }
                };
                let b_kj = &b_row[j];

                // Check if we need float mode
                if matches!(a_ik, Value::Float(_)) || matches!(b_kj, Value::Float(_)) {
                    is_float = true;
                }

                let prod = match (a_ik, b_kj) {
                    (Value::Int(x), Value::Int(y)) => Value::Int(x * y),
                    (Value::Float(x), Value::Float(y)) => Value::Float(x * y),
                    (Value::Int(x), Value::Float(y)) => Value::Float(*x as f64 * y),
                    (Value::Float(x), Value::Int(y)) => Value::Float(x * *y as f64),
                    _ => {
                        let ctx = ErrorContext::new()
                            .with_code(codes::TYPE_MISMATCH)
                            .with_help("matrix multiplication requires numeric elements");
                        return Err(CompileError::semantic_with_context(
                            format!("cannot multiply {} and {}", a_ik.type_name(), b_kj.type_name()),
                            ctx,
                        ));
                    }
                };

                sum = match (sum, prod) {
                    (Value::Int(s), Value::Int(p)) => Value::Int(s + p),
                    (Value::Float(s), Value::Float(p)) => Value::Float(s + p),
                    (Value::Int(s), Value::Float(p)) => Value::Float(s as f64 + p),
                    (Value::Float(s), Value::Int(p)) => Value::Float(s + p as f64),
                    _ => unreachable!(),
                };
            }

            // Convert to float if needed
            if is_float && matches!(sum, Value::Int(_)) {
                sum = Value::Float(sum.as_int()? as f64);
            }

            row.push(sum);
        }
        result.push(Value::Array(row));
    }

    Ok(Value::Array(result))
}

/// Multiply 2D matrix by 1D vector
fn matmul_matrix_vector(a: &[Value], b: &[Value]) -> Result<Value, CompileError> {
    let m = a.len();
    let n = match &a[0] {
        Value::Array(row) => row.len(),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("matrix-vector multiplication requires 2D matrix");
            return Err(CompileError::semantic_with_context(
                "first operand is not a 2D matrix",
                ctx,
            ));
        }
    };

    if n != b.len() {
        let ctx = ErrorContext::new()
            .with_code(codes::INVALID_OPERATION)
            .with_help(format!("matrix columns ({}) must match vector length ({})", n, b.len()));
        return Err(CompileError::semantic_with_context(
            format!("incompatible dimensions: ({}, {}) @ {}", m, n, b.len()),
            ctx,
        ));
    }

    let mut result = Vec::with_capacity(m);
    for i in 0..m {
        let a_row = match &a[i] {
            Value::Array(row) => row,
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help("matrix must have uniform rows");
                return Err(CompileError::semantic_with_context(
                    "matrix row is not an array",
                    ctx,
                ));
            }
        };
        let mut sum = Value::Int(0);
        let mut is_float = false;

        for k in 0..n {
            let a_ik = &a_row[k];
            let b_k = &b[k];

            if matches!(a_ik, Value::Float(_)) || matches!(b_k, Value::Float(_)) {
                is_float = true;
            }

            let prod = match (a_ik, b_k) {
                (Value::Int(x), Value::Int(y)) => Value::Int(x * y),
                (Value::Float(x), Value::Float(y)) => Value::Float(x * y),
                (Value::Int(x), Value::Float(y)) => Value::Float(*x as f64 * y),
                (Value::Float(x), Value::Int(y)) => Value::Float(x * *y as f64),
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::TYPE_MISMATCH)
                        .with_help("matrix-vector multiplication requires numeric elements");
                    return Err(CompileError::semantic_with_context(
                        format!("cannot multiply {} and {}", a_ik.type_name(), b_k.type_name()),
                        ctx,
                    ));
                }
            };

            sum = match (sum, prod) {
                (Value::Int(s), Value::Int(p)) => Value::Int(s + p),
                (Value::Float(s), Value::Float(p)) => Value::Float(s + p),
                (Value::Int(s), Value::Float(p)) => Value::Float(s as f64 + p),
                (Value::Float(s), Value::Int(p)) => Value::Float(s + p as f64),
                _ => unreachable!(),
            };
        }

        if is_float && matches!(sum, Value::Int(_)) {
            sum = Value::Float(sum.as_int()? as f64);
        }

        result.push(sum);
    }

    Ok(Value::Array(result))
}

/// Multiply 1D vector by 2D matrix
fn matmul_vector_matrix(a: &[Value], b: &[Value]) -> Result<Value, CompileError> {
    let m = a.len();
    let p = b.len();
    let q = match &b[0] {
        Value::Array(row) => row.len(),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("vector-matrix multiplication requires 2D matrix");
            return Err(CompileError::semantic_with_context(
                "second operand is not a 2D matrix",
                ctx,
            ));
        }
    };

    if m != p {
        let ctx = ErrorContext::new()
            .with_code(codes::INVALID_OPERATION)
            .with_help(format!("vector length ({}) must match matrix rows ({})", m, p));
        return Err(CompileError::semantic_with_context(
            format!("incompatible dimensions: {} @ ({}, {})", m, p, q),
            ctx,
        ));
    }

    let mut result = Vec::with_capacity(q);
    for j in 0..q {
        let mut sum = Value::Int(0);
        let mut is_float = false;

        for k in 0..m {
            let a_k = &a[k];
            let b_row = match &b[k] {
                Value::Array(row) => row,
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::TYPE_MISMATCH)
                        .with_help("matrix must have uniform rows");
                    return Err(CompileError::semantic_with_context(
                        "matrix row is not an array",
                        ctx,
                    ));
                }
            };
            let b_kj = &b_row[j];

            if matches!(a_k, Value::Float(_)) || matches!(b_kj, Value::Float(_)) {
                is_float = true;
            }

            let prod = match (a_k, b_kj) {
                (Value::Int(x), Value::Int(y)) => Value::Int(x * y),
                (Value::Float(x), Value::Float(y)) => Value::Float(x * y),
                (Value::Int(x), Value::Float(y)) => Value::Float(*x as f64 * y),
                (Value::Float(x), Value::Int(y)) => Value::Float(x * *y as f64),
                _ => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::TYPE_MISMATCH)
                        .with_help("vector-matrix multiplication requires numeric elements");
                    return Err(CompileError::semantic_with_context(
                        format!("cannot multiply {} and {}", a_k.type_name(), b_kj.type_name()),
                        ctx,
                    ));
                }
            };

            sum = match (sum, prod) {
                (Value::Int(s), Value::Int(p)) => Value::Int(s + p),
                (Value::Float(s), Value::Float(p)) => Value::Float(s + p),
                (Value::Int(s), Value::Float(p)) => Value::Float(s as f64 + p),
                (Value::Float(s), Value::Int(p)) => Value::Float(s + p as f64),
                _ => unreachable!(),
            };
        }

        if is_float && matches!(sum, Value::Int(_)) {
            sum = Value::Float(sum.as_int()? as f64);
        }

        result.push(sum);
    }

    Ok(Value::Array(result))
}
