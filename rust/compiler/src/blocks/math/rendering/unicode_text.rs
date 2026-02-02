//! Unicode text rendering for math expressions.
//!
//! Produces human-readable Unicode output using superscripts, subscripts,
//! and mathematical symbols.

use crate::blocks::math::ast::MathExpr;

/// Convert a MathExpr to Unicode text representation.
pub fn to_text(expr: &MathExpr) -> String {
    expr_to_text(expr)
}

fn expr_to_text(expr: &MathExpr) -> String {
    match expr {
        MathExpr::Int(n) => n.to_string(),
        MathExpr::Float(f) => {
            if f.fract() == 0.0 && f.abs() < 1e10 {
                format!("{:.0}", f)
            } else {
                f.to_string()
            }
        }
        MathExpr::Array(elements) => {
            if elements.is_empty() {
                return "[]".to_string();
            }
            if matches!(elements[0], MathExpr::Array(_)) {
                // Matrix
                let rows: Vec<String> = elements
                    .iter()
                    .map(|row| {
                        if let MathExpr::Array(cols) = row {
                            cols.iter().map(|e| expr_to_text(e)).collect::<Vec<_>>().join(", ")
                        } else {
                            expr_to_text(row)
                        }
                    })
                    .collect();
                format!("[{}]", rows.join("; "))
            } else {
                let items: Vec<String> = elements.iter().map(|e| expr_to_text(e)).collect();
                format!("[{}]", items.join(", "))
            }
        }

        MathExpr::Var(name) => var_to_unicode(name),

        MathExpr::Add(left, right) => {
            format!("{} + {}", expr_to_text(left), expr_to_text(right))
        }
        MathExpr::Sub(left, right) => {
            format!("{} - {}", expr_to_text(left), expr_to_text(right))
        }
        MathExpr::Mul(left, right) => {
            format!("{}\u{22c5}{}", expr_to_text(left), expr_to_text(right))
        }
        MathExpr::Div(left, right) => {
            format!("{}/{}", expr_to_text(left), expr_to_text(right))
        }
        MathExpr::Pow(base, exp) => {
            let base_str = expr_to_text(base);
            let exp_str = expr_to_text(exp);
            // Try to use Unicode superscript for simple cases
            if let Some(sup) = to_superscript(&exp_str) {
                format!("{}{}", base_str, sup)
            } else {
                format!("{}^({})", base_str, exp_str)
            }
        }
        MathExpr::Mod(left, right) => {
            format!("{} mod {}", expr_to_text(left), expr_to_text(right))
        }

        MathExpr::Neg(inner) => format!("-{}", expr_to_text(inner)),
        MathExpr::Abs(inner) => format!("|{}|", expr_to_text(inner)),

        MathExpr::App(name, args) => app_to_text(name, args),

        MathExpr::Subscript(base, index) => {
            let base_str = expr_to_text(base);
            let idx_str = expr_to_text(index);
            if let Some(sub) = to_subscript(&idx_str) {
                format!("{}{}", base_str, sub)
            } else {
                format!("{}[{}]", base_str, idx_str)
            }
        }

        MathExpr::Group(inner) => format!("({})", expr_to_text(inner)),

        MathExpr::Sum { var, range, body } => {
            let var_sub = to_subscript(var).unwrap_or_else(|| var.clone());
            format!(
                "\u{03a3}({}={})^({}) {}",
                var_sub,
                expr_to_text(&range.start),
                expr_to_text(&range.end),
                expr_to_text(body)
            )
        }
        MathExpr::Prod { var, range, body } => {
            let var_sub = to_subscript(var).unwrap_or_else(|| var.clone());
            format!(
                "\u{03a0}({}={})^({}) {}",
                var_sub,
                expr_to_text(&range.start),
                expr_to_text(&range.end),
                expr_to_text(body)
            )
        }
        MathExpr::Integral { var, range, body } => {
            format!(
                "\u{222b}[{},{}] {} d{}",
                expr_to_text(&range.start),
                expr_to_text(&range.end),
                expr_to_text(body),
                var
            )
        }

        MathExpr::Eq(l, r) => format!("{} = {}", expr_to_text(l), expr_to_text(r)),
        MathExpr::Neq(l, r) => format!("{} \u{2260} {}", expr_to_text(l), expr_to_text(r)),
        MathExpr::Lt(l, r) => format!("{} < {}", expr_to_text(l), expr_to_text(r)),
        MathExpr::Le(l, r) => format!("{} \u{2264} {}", expr_to_text(l), expr_to_text(r)),
        MathExpr::Gt(l, r) => format!("{} > {}", expr_to_text(l), expr_to_text(r)),
        MathExpr::Ge(l, r) => format!("{} \u{2265} {}", expr_to_text(l), expr_to_text(r)),
        MathExpr::Approx(l, r) => format!("{} \u{2248} {}", expr_to_text(l), expr_to_text(r)),
    }
}

fn var_to_unicode(name: &str) -> String {
    match name {
        "alpha" => "\u{03b1}".to_string(),
        "beta" => "\u{03b2}".to_string(),
        "gamma" => "\u{03b3}".to_string(),
        "delta" => "\u{03b4}".to_string(),
        "epsilon" => "\u{03b5}".to_string(),
        "theta" => "\u{03b8}".to_string(),
        "lambda" => "\u{03bb}".to_string(),
        "mu" => "\u{03bc}".to_string(),
        "pi" => "\u{03c0}".to_string(),
        "sigma" => "\u{03c3}".to_string(),
        "tau" => "\u{03c4}".to_string(),
        "phi" => "\u{03c6}".to_string(),
        "omega" => "\u{03c9}".to_string(),
        "inf" => "\u{221e}".to_string(),
        _ => name.to_string(),
    }
}

fn app_to_text(name: &str, args: &[MathExpr]) -> String {
    match name {
        "frac" if args.len() == 2 => {
            let n = expr_to_text(&args[0]);
            let d = expr_to_text(&args[1]);
            // Simple fraction: try Unicode vulgar fractions for common cases
            match (n.as_str(), d.as_str()) {
                ("1", "2") => "\u{00bd}".to_string(),
                ("1", "3") => "\u{2153}".to_string(),
                ("2", "3") => "\u{2154}".to_string(),
                ("1", "4") => "\u{00bc}".to_string(),
                ("3", "4") => "\u{00be}".to_string(),
                _ => format!("{}/{}", n, d),
            }
        }
        "sqrt" if args.len() == 1 => format!("\u{221a}({})", expr_to_text(&args[0])),
        "cbrt" if args.len() == 1 => format!("\u{221b}({})", expr_to_text(&args[0])),
        "abs" if args.len() == 1 => format!("|{}|", expr_to_text(&args[0])),
        _ => {
            let args_str: Vec<String> = args.iter().map(|a| expr_to_text(a)).collect();
            format!("{}({})", name, args_str.join(", "))
        }
    }
}

/// Convert a string to Unicode superscript characters where possible.
fn to_superscript(s: &str) -> Option<String> {
    let mut result = String::new();
    for ch in s.chars() {
        match ch {
            '0' => result.push('\u{2070}'),
            '1' => result.push('\u{00b9}'),
            '2' => result.push('\u{00b2}'),
            '3' => result.push('\u{00b3}'),
            '4' => result.push('\u{2074}'),
            '5' => result.push('\u{2075}'),
            '6' => result.push('\u{2076}'),
            '7' => result.push('\u{2077}'),
            '8' => result.push('\u{2078}'),
            '9' => result.push('\u{2079}'),
            '+' => result.push('\u{207a}'),
            '-' => result.push('\u{207b}'),
            'n' => result.push('\u{207f}'),
            'i' => result.push('\u{2071}'),
            _ => return None,
        }
    }
    Some(result)
}

/// Convert a string to Unicode subscript characters where possible.
fn to_subscript(s: &str) -> Option<String> {
    let mut result = String::new();
    for ch in s.chars() {
        match ch {
            '0' => result.push('\u{2080}'),
            '1' => result.push('\u{2081}'),
            '2' => result.push('\u{2082}'),
            '3' => result.push('\u{2083}'),
            '4' => result.push('\u{2084}'),
            '5' => result.push('\u{2085}'),
            '6' => result.push('\u{2086}'),
            '7' => result.push('\u{2087}'),
            '8' => result.push('\u{2088}'),
            '9' => result.push('\u{2089}'),
            '+' => result.push('\u{208a}'),
            '-' => result.push('\u{208b}'),
            'i' => result.push('\u{1d62}'),
            'n' => result.push('\u{2099}'),
            _ => return None,
        }
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blocks::math::ast::Range;

    #[test]
    fn test_text_int() {
        assert_eq!(to_text(&MathExpr::Int(42)), "42");
    }

    #[test]
    fn test_text_add() {
        let expr = MathExpr::Add(Box::new(MathExpr::Int(2)), Box::new(MathExpr::Int(3)));
        assert_eq!(to_text(&expr), "2 + 3");
    }

    #[test]
    fn test_text_pow_superscript() {
        let expr = MathExpr::Pow(Box::new(MathExpr::Var("x".to_string())), Box::new(MathExpr::Int(2)));
        assert_eq!(to_text(&expr), "x\u{00b2}");
    }

    #[test]
    fn test_text_sqrt() {
        let expr = MathExpr::App("sqrt".to_string(), vec![MathExpr::Var("pi".to_string())]);
        assert_eq!(to_text(&expr), "\u{221a}(\u{03c0})");
    }

    #[test]
    fn test_text_frac_half() {
        let expr = MathExpr::App("frac".to_string(), vec![MathExpr::Int(1), MathExpr::Int(2)]);
        assert_eq!(to_text(&expr), "\u{00bd}");
    }

    #[test]
    fn test_text_greek() {
        assert_eq!(to_text(&MathExpr::Var("pi".to_string())), "\u{03c0}");
        assert_eq!(to_text(&MathExpr::Var("alpha".to_string())), "\u{03b1}");
    }

    #[test]
    fn test_text_sum() {
        let expr = MathExpr::Sum {
            var: "i".to_string(),
            range: Box::new(Range::new(MathExpr::Int(1), MathExpr::Var("n".to_string()))),
            body: Box::new(MathExpr::Pow(
                Box::new(MathExpr::Var("i".to_string())),
                Box::new(MathExpr::Int(2)),
            )),
        };
        let text = to_text(&expr);
        assert!(text.contains("\u{03a3}"));
        assert!(text.contains("\u{00b2}"));
    }

    #[test]
    fn test_text_comparison() {
        let expr = MathExpr::Le(Box::new(MathExpr::Var("x".to_string())), Box::new(MathExpr::Int(5)));
        assert_eq!(to_text(&expr), "x \u{2264} 5");
    }
}
