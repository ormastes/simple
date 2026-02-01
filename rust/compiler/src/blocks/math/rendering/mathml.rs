//! MathML rendering for math expressions.

use crate::blocks::math::ast::MathExpr;

/// Convert a MathExpr to MathML format.
pub fn to_mathml(expr: &MathExpr) -> String {
    format!("<math>{}</math>", expr_to_mathml(expr))
}

fn expr_to_mathml(expr: &MathExpr) -> String {
    match expr {
        MathExpr::Int(n) => format!("<mn>{}</mn>", n),
        MathExpr::Float(f) => {
            if f.fract() == 0.0 && f.abs() < 1e10 {
                format!("<mn>{:.0}</mn>", f)
            } else {
                format!("<mn>{}</mn>", f)
            }
        }
        MathExpr::Array(elements) => {
            if elements.is_empty() {
                return "<mrow><mo>[</mo><mo>]</mo></mrow>".to_string();
            }
            // Check if matrix (array of arrays)
            if matches!(elements[0], MathExpr::Array(_)) {
                let rows: Vec<String> = elements
                    .iter()
                    .map(|row| {
                        let cols = if let MathExpr::Array(cols) = row {
                            cols.iter()
                                .map(|e| format!("<mtd>{}</mtd>", expr_to_mathml(e)))
                                .collect::<Vec<_>>()
                                .join("")
                        } else {
                            format!("<mtd>{}</mtd>", expr_to_mathml(row))
                        };
                        format!("<mtr>{}</mtr>", cols)
                    })
                    .collect();
                format!(
                    "<mrow><mo>[</mo><mtable>{}</mtable><mo>]</mo></mrow>",
                    rows.join("")
                )
            } else {
                // Column vector
                let rows: Vec<String> = elements
                    .iter()
                    .map(|e| format!("<mtr><mtd>{}</mtd></mtr>", expr_to_mathml(e)))
                    .collect();
                format!(
                    "<mrow><mo>[</mo><mtable>{}</mtable><mo>]</mo></mrow>",
                    rows.join("")
                )
            }
        }

        MathExpr::Var(name) => var_to_mathml(name),

        MathExpr::Add(left, right) => format!(
            "<mrow>{}<mo>+</mo>{}</mrow>",
            expr_to_mathml(left),
            expr_to_mathml(right)
        ),
        MathExpr::Sub(left, right) => format!(
            "<mrow>{}<mo>-</mo>{}</mrow>",
            expr_to_mathml(left),
            expr_to_mathml(right)
        ),
        MathExpr::Mul(left, right) => format!(
            "<mrow>{}<mo>&InvisibleTimes;</mo>{}</mrow>",
            expr_to_mathml(left),
            expr_to_mathml(right)
        ),
        MathExpr::Div(left, right) => format!(
            "<mfrac>{}{}</mfrac>",
            expr_to_mathml(left),
            expr_to_mathml(right)
        ),
        MathExpr::Pow(base, exp) => format!(
            "<msup>{}{}</msup>",
            expr_to_mathml(base),
            expr_to_mathml(exp)
        ),
        MathExpr::Mod(left, right) => format!(
            "<mrow>{}<mo>mod</mo>{}</mrow>",
            expr_to_mathml(left),
            expr_to_mathml(right)
        ),

        MathExpr::Neg(inner) => format!("<mrow><mo>-</mo>{}</mrow>", expr_to_mathml(inner)),
        MathExpr::Abs(inner) => format!(
            "<mrow><mo>|</mo>{}<mo>|</mo></mrow>",
            expr_to_mathml(inner)
        ),

        MathExpr::App(name, args) => app_to_mathml(name, args),

        MathExpr::Subscript(base, index) => format!(
            "<msub>{}{}</msub>",
            expr_to_mathml(base),
            expr_to_mathml(index)
        ),

        MathExpr::Group(inner) => format!(
            "<mrow><mo>(</mo>{}<mo>)</mo></mrow>",
            expr_to_mathml(inner)
        ),

        MathExpr::Sum { var, range, body } => format!(
            "<mrow><munderover><mo>&Sum;</mo><mrow><mi>{}</mi><mo>=</mo>{}</mrow>{}</munderover>{}</mrow>",
            var,
            expr_to_mathml(&range.start),
            expr_to_mathml(&range.end),
            expr_to_mathml(body)
        ),
        MathExpr::Prod { var, range, body } => format!(
            "<mrow><munderover><mo>&Product;</mo><mrow><mi>{}</mi><mo>=</mo>{}</mrow>{}</munderover>{}</mrow>",
            var,
            expr_to_mathml(&range.start),
            expr_to_mathml(&range.end),
            expr_to_mathml(body)
        ),
        MathExpr::Integral { var, range, body } => format!(
            "<mrow><msubsup><mo>&Integral;</mo>{}{}</msubsup>{}<mo>&dd;</mo><mi>{}</mi></mrow>",
            expr_to_mathml(&range.start),
            expr_to_mathml(&range.end),
            expr_to_mathml(body),
            var
        ),

        MathExpr::Eq(l, r) => format!(
            "<mrow>{}<mo>=</mo>{}</mrow>",
            expr_to_mathml(l),
            expr_to_mathml(r)
        ),
        MathExpr::Neq(l, r) => format!(
            "<mrow>{}<mo>&ne;</mo>{}</mrow>",
            expr_to_mathml(l),
            expr_to_mathml(r)
        ),
        MathExpr::Lt(l, r) => format!(
            "<mrow>{}<mo>&lt;</mo>{}</mrow>",
            expr_to_mathml(l),
            expr_to_mathml(r)
        ),
        MathExpr::Le(l, r) => format!(
            "<mrow>{}<mo>&le;</mo>{}</mrow>",
            expr_to_mathml(l),
            expr_to_mathml(r)
        ),
        MathExpr::Gt(l, r) => format!(
            "<mrow>{}<mo>&gt;</mo>{}</mrow>",
            expr_to_mathml(l),
            expr_to_mathml(r)
        ),
        MathExpr::Ge(l, r) => format!(
            "<mrow>{}<mo>&ge;</mo>{}</mrow>",
            expr_to_mathml(l),
            expr_to_mathml(r)
        ),
        MathExpr::Approx(l, r) => format!(
            "<mrow>{}<mo>&approx;</mo>{}</mrow>",
            expr_to_mathml(l),
            expr_to_mathml(r)
        ),
    }
}

fn var_to_mathml(name: &str) -> String {
    match name {
        "alpha" => "<mi>&alpha;</mi>".to_string(),
        "beta" => "<mi>&beta;</mi>".to_string(),
        "gamma" => "<mi>&gamma;</mi>".to_string(),
        "delta" => "<mi>&delta;</mi>".to_string(),
        "epsilon" => "<mi>&epsilon;</mi>".to_string(),
        "theta" => "<mi>&theta;</mi>".to_string(),
        "lambda" => "<mi>&lambda;</mi>".to_string(),
        "mu" => "<mi>&mu;</mi>".to_string(),
        "pi" => "<mi>&pi;</mi>".to_string(),
        "sigma" => "<mi>&sigma;</mi>".to_string(),
        "tau" => "<mi>&tau;</mi>".to_string(),
        "phi" => "<mi>&phi;</mi>".to_string(),
        "omega" => "<mi>&omega;</mi>".to_string(),
        _ => format!("<mi>{}</mi>", name),
    }
}

fn app_to_mathml(name: &str, args: &[MathExpr]) -> String {
    match name {
        "frac" if args.len() == 2 => format!(
            "<mfrac>{}{}</mfrac>",
            expr_to_mathml(&args[0]),
            expr_to_mathml(&args[1])
        ),
        "sqrt" if args.len() == 1 => format!("<msqrt>{}</msqrt>", expr_to_mathml(&args[0])),
        "root" if args.len() == 2 => format!(
            "<mroot>{}{}</mroot>",
            expr_to_mathml(&args[0]),
            expr_to_mathml(&args[1])
        ),
        "abs" if args.len() == 1 => format!(
            "<mrow><mo>|</mo>{}<mo>|</mo></mrow>",
            expr_to_mathml(&args[0])
        ),
        "sin" | "cos" | "tan" | "log" | "ln" | "exp" | "sinh" | "cosh" | "tanh"
        | "asin" | "acos" | "atan" | "arcsin" | "arccos" | "arctan" => {
            let args_ml: Vec<String> = args.iter().map(|a| expr_to_mathml(a)).collect();
            format!(
                "<mrow><mi>{}</mi><mo>&ApplyFunction;</mo><mrow><mo>(</mo>{}<mo>)</mo></mrow></mrow>",
                name,
                args_ml.join("<mo>,</mo>")
            )
        }
        _ => {
            let args_ml: Vec<String> = args.iter().map(|a| expr_to_mathml(a)).collect();
            format!(
                "<mrow><mi>{}</mi><mo>(</mo>{}<mo>)</mo></mrow>",
                name,
                args_ml.join("<mo>,</mo>")
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blocks::math::ast::Range;

    #[test]
    fn test_mathml_int() {
        let expr = MathExpr::Int(42);
        assert_eq!(to_mathml(&expr), "<math><mn>42</mn></math>");
    }

    #[test]
    fn test_mathml_add() {
        let expr = MathExpr::Add(Box::new(MathExpr::Int(2)), Box::new(MathExpr::Int(3)));
        assert_eq!(
            to_mathml(&expr),
            "<math><mrow><mn>2</mn><mo>+</mo><mn>3</mn></mrow></math>"
        );
    }

    #[test]
    fn test_mathml_frac() {
        let expr = MathExpr::App("frac".to_string(), vec![MathExpr::Int(1), MathExpr::Int(2)]);
        assert_eq!(
            to_mathml(&expr),
            "<math><mfrac><mn>1</mn><mn>2</mn></mfrac></math>"
        );
    }

    #[test]
    fn test_mathml_sqrt() {
        let expr = MathExpr::App("sqrt".to_string(), vec![MathExpr::Int(16)]);
        assert_eq!(
            to_mathml(&expr),
            "<math><msqrt><mn>16</mn></msqrt></math>"
        );
    }

    #[test]
    fn test_mathml_pow() {
        let expr = MathExpr::Pow(
            Box::new(MathExpr::Var("x".to_string())),
            Box::new(MathExpr::Int(2)),
        );
        assert_eq!(
            to_mathml(&expr),
            "<math><msup><mi>x</mi><mn>2</mn></msup></math>"
        );
    }

    #[test]
    fn test_mathml_greek() {
        let expr = MathExpr::Var("pi".to_string());
        assert_eq!(to_mathml(&expr), "<math><mi>&pi;</mi></math>");
    }

    #[test]
    fn test_mathml_sum() {
        let expr = MathExpr::Sum {
            var: "i".to_string(),
            range: Box::new(Range::new(MathExpr::Int(1), MathExpr::Var("n".to_string()))),
            body: Box::new(MathExpr::Var("i".to_string())),
        };
        let result = to_mathml(&expr);
        assert!(result.contains("&Sum;"));
        assert!(result.contains("<mi>i</mi>"));
    }

    #[test]
    fn test_mathml_integral() {
        let expr = MathExpr::Integral {
            var: "x".to_string(),
            range: Box::new(Range::new(MathExpr::Int(0), MathExpr::Int(1))),
            body: Box::new(MathExpr::Var("x".to_string())),
        };
        let result = to_mathml(&expr);
        assert!(result.contains("&Integral;"));
        assert!(result.contains("&dd;"));
    }
}
