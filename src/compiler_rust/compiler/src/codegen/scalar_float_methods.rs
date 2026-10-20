//! Single source of truth for scalar float builtin methods (`x.sqrt()`,
//! `x.abs()`, `x.sin()`, ...), shared by the Cranelift and LLVM backends so a
//! method one backend accepts cannot be rejected by the other.

/// Methods both backends lower to a native float operation (a Cranelift
/// instruction / an LLVM intrinsic).
pub(crate) fn is_native_unary(method: &str) -> bool {
    native_intrinsic_stem(method).is_some()
}

/// LLVM intrinsic stem (`llvm.<stem>.f64`) for a native unary float method.
pub(crate) fn native_intrinsic_stem(method: &str) -> Option<&'static str> {
    match method {
        "sqrt" => Some("sqrt"),
        "abs" => Some("fabs"),
        "floor" => Some("floor"),
        "ceil" => Some("ceil"),
        "round" => Some("round"),
        "trunc" => Some("trunc"),
        _ => None,
    }
}

/// `f64 -> f64` runtime symbol for float methods with no native instruction.
pub(crate) fn rt_math_unary(method: &str) -> Option<&'static str> {
    match method {
        "sin" => Some("rt_math_sin"),
        "cos" => Some("rt_math_cos"),
        "tan" => Some("rt_math_tan"),
        "asin" => Some("rt_math_asin"),
        "acos" => Some("rt_math_acos"),
        "atan" => Some("rt_math_atan"),
        "sinh" => Some("rt_math_sinh"),
        "cosh" => Some("rt_math_cosh"),
        "tanh" => Some("rt_math_tanh"),
        "exp" => Some("rt_math_exp"),
        "ln" => Some("rt_math_log"),
        "log2" => Some("rt_math_log2"),
        "log10" => Some("rt_math_log10"),
        "cbrt" => Some("rt_math_cbrt"),
        // Language semantics: ties round away from zero (interpreter, `rt_math_round`).
        // Cranelift has no such instruction (`nearest` ties to even), so it calls this;
        // LLVM uses the `llvm.round` intrinsic, which has the same semantics.
        "round" => Some("rt_math_round"),
        _ => None,
    }
}

/// `(f64, f64) -> f64` runtime symbol for binary float methods.
pub(crate) fn rt_math_binary(method: &str) -> Option<&'static str> {
    match method {
        "pow" | "powf" => Some("rt_math_pow"),
        "max" => Some("rt_math_max"),
        "min" => Some("rt_math_min"),
        "atan2" => Some("rt_math_atan2"),
        "hypot" => Some("rt_math_hypot"),
        _ => None,
    }
}
