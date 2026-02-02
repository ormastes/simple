//! Lean4 rendering for math expressions.
//!
//! Generates Lean4 theorem prover syntax from MathExpr AST.

use crate::blocks::math::ast::MathExpr;

/// Convert a MathExpr to Lean4 syntax.
pub fn to_lean(expr: &MathExpr) -> String {
    expr_to_lean(expr)
}

fn expr_to_lean(expr: &MathExpr) -> String {
    match expr {
        MathExpr::Int(n) => {
            if *n < 0 {
                format!("({})", n)
            } else {
                n.to_string()
            }
        }
        MathExpr::Float(f) => {
            if f.fract() == 0.0 && f.abs() < 1e10 {
                format!("({:.0} : Float)", f)
            } else {
                format!("({} : Float)", f)
            }
        }
        MathExpr::Array(elements) => {
            if elements.is_empty() {
                return "[]".to_string();
            }
            if matches!(elements[0], MathExpr::Array(_)) {
                // Matrix: !![a, b; c, d]
                let rows: Vec<String> = elements
                    .iter()
                    .map(|row| {
                        if let MathExpr::Array(cols) = row {
                            cols.iter().map(|e| expr_to_lean(e)).collect::<Vec<_>>().join(", ")
                        } else {
                            expr_to_lean(row)
                        }
                    })
                    .collect();
                format!("!![{}]", rows.join("; "))
            } else {
                let items: Vec<String> = elements.iter().map(|e| expr_to_lean(e)).collect();
                format!("[{}]", items.join(", "))
            }
        }

        MathExpr::Var(name) => var_to_lean(name),

        MathExpr::Add(left, right) => {
            format!("{} + {}", expr_to_lean(left), expr_to_lean(right))
        }
        MathExpr::Sub(left, right) => {
            format!("{} - {}", expr_to_lean(left), expr_to_lean(right))
        }
        MathExpr::Mul(left, right) => {
            format!("{} * {}", expr_to_lean(left), expr_to_lean(right))
        }
        MathExpr::Div(left, right) => {
            format!("{} / {}", expr_to_lean(left), expr_to_lean(right))
        }
        MathExpr::Pow(base, exp) => {
            format!("{} ^ {}", expr_to_lean(base), expr_to_lean(exp))
        }
        MathExpr::Mod(left, right) => {
            format!("{} % {}", expr_to_lean(left), expr_to_lean(right))
        }

        MathExpr::Neg(inner) => format!("-({})", expr_to_lean(inner)),
        MathExpr::Abs(inner) => format!("|{}|", expr_to_lean(inner)),

        MathExpr::App(name, args) => app_to_lean(name, args),

        MathExpr::Subscript(base, index) => {
            format!("{}[{}]", expr_to_lean(base), expr_to_lean(index))
        }

        MathExpr::Group(inner) => format!("({})", expr_to_lean(inner)),

        MathExpr::Sum { var, range, body } => {
            format!(
                "(\u{2211} {} in Finset.Icc {} {}, {})",
                var,
                expr_to_lean(&range.start),
                expr_to_lean(&range.end),
                expr_to_lean(body)
            )
        }
        MathExpr::Prod { var, range, body } => {
            format!(
                "(\u{220f} {} in Finset.Icc {} {}, {})",
                var,
                expr_to_lean(&range.start),
                expr_to_lean(&range.end),
                expr_to_lean(body)
            )
        }
        MathExpr::Integral { var, range, body } => {
            format!(
                "(MeasureTheory.integral (fun {} => {}) {} {})",
                var,
                expr_to_lean(body),
                expr_to_lean(&range.start),
                expr_to_lean(&range.end)
            )
        }

        MathExpr::Eq(l, r) => format!("{} = {}", expr_to_lean(l), expr_to_lean(r)),
        MathExpr::Neq(l, r) => format!("{} \u{2260} {}", expr_to_lean(l), expr_to_lean(r)),
        MathExpr::Lt(l, r) => format!("{} < {}", expr_to_lean(l), expr_to_lean(r)),
        MathExpr::Le(l, r) => format!("{} \u{2264} {}", expr_to_lean(l), expr_to_lean(r)),
        MathExpr::Gt(l, r) => format!("{} > {}", expr_to_lean(l), expr_to_lean(r)),
        MathExpr::Ge(l, r) => format!("{} \u{2265} {}", expr_to_lean(l), expr_to_lean(r)),
        MathExpr::Approx(l, r) => {
            // No standard approx in Lean, use abs diff
            format!("|{} - {}| < \u{03b5}", expr_to_lean(l), expr_to_lean(r))
        }
    }
}

fn var_to_lean(name: &str) -> String {
    match name {
        "alpha" => "\u{03b1}".to_string(),
        "beta" => "\u{03b2}".to_string(),
        "gamma" => "\u{03b3}".to_string(),
        "delta" => "\u{03b4}".to_string(),
        "epsilon" => "\u{03b5}".to_string(),
        "theta" => "\u{03b8}".to_string(),
        "lambda" => "\u{03bb}".to_string(),
        "mu" => "\u{03bc}".to_string(),
        "pi" => "Real.pi".to_string(),
        "sigma" => "\u{03c3}".to_string(),
        "tau" => "\u{03c4}".to_string(),
        "phi" => "\u{03c6}".to_string(),
        "omega" => "\u{03c9}".to_string(),
        "inf" => "\u{22a4}".to_string(), // top/infinity
        "e" => "Real.exp 1".to_string(),
        _ => name.to_string(),
    }
}

fn app_to_lean(name: &str, args: &[MathExpr]) -> String {
    match name {
        "frac" if args.len() == 2 => {
            format!("{} / {}", expr_to_lean(&args[0]), expr_to_lean(&args[1]))
        }
        "sqrt" if args.len() == 1 => format!("Real.sqrt {}", lean_arg(&args[0])),
        "cbrt" if args.len() == 1 => format!("{} ^ (1/3 : Float)", lean_arg(&args[0])),
        "abs" if args.len() == 1 => format!("|{}|", expr_to_lean(&args[0])),
        "sin" if args.len() == 1 => format!("Real.sin {}", lean_arg(&args[0])),
        "cos" if args.len() == 1 => format!("Real.cos {}", lean_arg(&args[0])),
        "tan" if args.len() == 1 => format!("Real.tan {}", lean_arg(&args[0])),
        "exp" if args.len() == 1 => format!("Real.exp {}", lean_arg(&args[0])),
        "log" | "ln" if args.len() == 1 => format!("Real.log {}", lean_arg(&args[0])),
        "log10" if args.len() == 1 => {
            format!("Real.log {} / Real.log 10", lean_arg(&args[0]))
        }
        "log2" if args.len() == 1 => {
            format!("Real.log {} / Real.log 2", lean_arg(&args[0]))
        }
        "factorial" | "fact" if args.len() == 1 => format!("Nat.factorial {}", lean_arg(&args[0])),
        "binomial" | "binom" if args.len() == 2 => {
            format!("Nat.choose {} {}", lean_arg(&args[0]), lean_arg(&args[1]))
        }
        "min" if args.len() == 2 => {
            format!("min {} {}", lean_arg(&args[0]), lean_arg(&args[1]))
        }
        "max" if args.len() == 2 => {
            format!("max {} {}", lean_arg(&args[0]), lean_arg(&args[1]))
        }
        "gcd" if args.len() == 2 => {
            format!("Nat.gcd {} {}", lean_arg(&args[0]), lean_arg(&args[1]))
        }
        "lcm" if args.len() == 2 => {
            format!("Nat.lcm {} {}", lean_arg(&args[0]), lean_arg(&args[1]))
        }
        _ => {
            let args_str: Vec<String> = args.iter().map(|a| lean_arg(a)).collect();
            format!("{} {}", name, args_str.join(" "))
        }
    }
}

/// Wrap argument in parens if it's complex.
fn lean_arg(expr: &MathExpr) -> String {
    match expr {
        MathExpr::Int(n) if *n >= 0 => n.to_string(),
        MathExpr::Var(_) => expr_to_lean(expr),
        _ => format!("({})", expr_to_lean(expr)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blocks::math::ast::Range;

    #[test]
    fn test_lean_int() {
        assert_eq!(to_lean(&MathExpr::Int(42)), "42");
    }

    #[test]
    fn test_lean_add() {
        let expr = MathExpr::Add(Box::new(MathExpr::Int(2)), Box::new(MathExpr::Int(3)));
        assert_eq!(to_lean(&expr), "2 + 3");
    }

    #[test]
    fn test_lean_pow() {
        let expr = MathExpr::Pow(Box::new(MathExpr::Var("x".to_string())), Box::new(MathExpr::Int(2)));
        assert_eq!(to_lean(&expr), "x ^ 2");
    }

    #[test]
    fn test_lean_sqrt() {
        let expr = MathExpr::App("sqrt".to_string(), vec![MathExpr::Var("x".to_string())]);
        assert_eq!(to_lean(&expr), "Real.sqrt x");
    }

    #[test]
    fn test_lean_frac() {
        let expr = MathExpr::App("frac".to_string(), vec![MathExpr::Int(1), MathExpr::Int(2)]);
        assert_eq!(to_lean(&expr), "1 / 2");
    }

    #[test]
    fn test_lean_pi() {
        assert_eq!(to_lean(&MathExpr::Var("pi".to_string())), "Real.pi");
    }

    #[test]
    fn test_lean_sum() {
        let expr = MathExpr::Sum {
            var: "i".to_string(),
            range: Box::new(Range::new(MathExpr::Int(1), MathExpr::Var("n".to_string()))),
            body: Box::new(MathExpr::Pow(
                Box::new(MathExpr::Var("i".to_string())),
                Box::new(MathExpr::Int(2)),
            )),
        };
        let result = to_lean(&expr);
        assert!(result.contains("\u{2211}"));
        assert!(result.contains("Finset.Icc"));
        assert!(result.contains("i ^ 2"));
    }

    #[test]
    fn test_lean_factorial() {
        let expr = MathExpr::App("factorial".to_string(), vec![MathExpr::Int(5)]);
        assert_eq!(to_lean(&expr), "Nat.factorial 5");
    }

    #[test]
    fn test_lean_sin() {
        let expr = MathExpr::App("sin".to_string(), vec![MathExpr::Var("x".to_string())]);
        assert_eq!(to_lean(&expr), "Real.sin x");
    }

    #[test]
    fn test_lean_negative() {
        assert_eq!(to_lean(&MathExpr::Int(-5)), "(-5)");
    }
}
