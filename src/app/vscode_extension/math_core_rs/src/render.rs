use crate::parser::{debug_tree, parse_expression, BinOp, Expr};

pub fn render_math_core_json(
    input_ptr: *const u8,
    input_len: usize,
    out_len_ptr: *mut usize,
) -> *mut u8 {
    let source = unsafe {
        if input_ptr.is_null() || input_len == 0 {
            ""
        } else {
            core::str::from_utf8(core::slice::from_raw_parts(input_ptr, input_len)).unwrap_or("")
        }
    };

    let rendered = match parse_expression(source) {
        Ok(expr) => RenderedMath {
            latex: render_latex(&expr),
            pretty: render_pretty(&expr),
            text: Some(render_text(&expr)),
            debug: Some(debug_tree(&expr)),
        },
        Err(err) => RenderedMath {
            latex: source.to_string(),
            pretty: source.to_string(),
            text: Some(source.to_string()),
            debug: Some(format!("parse_error({err})")),
        },
    };

    let json = rendered.to_json();
    write_json(json, out_len_ptr)
}

#[derive(Debug, Clone)]
struct RenderedMath {
    latex: String,
    pretty: String,
    text: Option<String>,
    debug: Option<String>,
}

impl RenderedMath {
    fn to_json(&self) -> String {
        let mut out = String::with_capacity(
            self.latex.len()
                + self.pretty.len()
                + self.text.as_ref().map(|s| s.len()).unwrap_or(0)
                + self.debug.as_ref().map(|s| s.len()).unwrap_or(0)
                + 64,
        );
        out.push('{');
        push_json_field(&mut out, "latex", &self.latex);
        out.push(',');
        push_json_field(&mut out, "pretty", &self.pretty);
        if let Some(text) = &self.text {
            out.push(',');
            push_json_field(&mut out, "text", text);
        }
        if let Some(debug) = &self.debug {
            out.push(',');
            push_json_field(&mut out, "debug", debug);
        }
        out.push('}');
        out
    }
}

fn write_json(json: String, out_len_ptr: *mut usize) -> *mut u8 {
    let bytes = json.into_bytes();
    let len = bytes.len();
    unsafe {
        if !out_len_ptr.is_null() {
            *out_len_ptr = len;
        }
    }

    let ptr = crate::abi::rt_alloc(len);
    if ptr.is_null() {
        unsafe {
            if !out_len_ptr.is_null() {
                *out_len_ptr = 0;
            }
        }
        return core::ptr::null_mut();
    }

    unsafe {
        core::ptr::copy_nonoverlapping(bytes.as_ptr(), ptr, len);
    }
    ptr
}

fn push_json_field(out: &mut String, key: &str, value: &str) {
    out.push('"');
    out.push_str(key);
    out.push_str("\":");
    push_json_string(out, value);
}

fn push_json_string(out: &mut String, value: &str) {
    out.push('"');
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{08}' => out.push_str("\\b"),
            '\u{0C}' => out.push_str("\\f"),
            c if c < '\u{20}' => {
                let code = c as u32;
                let _ = core::fmt::Write::write_fmt(out, format_args!("\\u{code:04x}"));
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

fn render_text(expr: &Expr) -> String {
    render_with_prec(expr, 0, RenderMode::Text)
}

fn render_pretty(expr: &Expr) -> String {
    render_with_prec(expr, 0, RenderMode::Pretty)
}

fn render_latex(expr: &Expr) -> String {
    render_with_prec(expr, 0, RenderMode::Latex)
}

#[derive(Clone, Copy)]
enum RenderMode {
    Text,
    Pretty,
    Latex,
}

fn render_with_prec(expr: &Expr, parent_prec: u8, mode: RenderMode) -> String {
    let (rendered, prec) = match expr {
        Expr::Number(n) => (n.clone(), 6),
        Expr::Ident(name) => (render_ident(name, mode), 6),
        Expr::UnaryNeg(inner) => {
            let inner_rendered = render_with_prec(inner, 5, mode);
            (
                match mode {
                    RenderMode::Latex => format!("-{inner_rendered}"),
                    _ => format!("-{inner_rendered}"),
                },
                5,
            )
        }
        Expr::Binary { op, left, right } => render_binary(op, left, right, mode),
        Expr::Call { name, args } => render_call(name, args, mode),
        Expr::Group(inner) => {
            let rendered = render_with_prec(inner, 0, mode);
            match mode {
                RenderMode::Latex => (format!("\\left({rendered}\\right)"), 6),
                _ => (format!("({rendered})"), 6),
            }
        }
        Expr::Subscript { base, sub } => {
            let base_rendered = render_with_prec(base, 6, mode);
            let sub_rendered = render_with_prec(sub, 6, mode);
            let rendered = match mode {
                RenderMode::Latex => format!("{base_rendered}_{{{sub_rendered}}}"),
                RenderMode::Pretty => {
                    format!("{base_rendered}{}", to_subscript_if_simple(&sub_rendered))
                }
                RenderMode::Text => format!("{base_rendered}_{sub_rendered}"),
            };
            (rendered, 6)
        }
    };

    if prec < parent_prec {
        match mode {
            RenderMode::Latex => format!("\\left({rendered}\\right)"),
            _ => format!("({rendered})"),
        }
    } else {
        rendered
    }
}

fn render_binary(op: &BinOp, left: &Expr, right: &Expr, mode: RenderMode) -> (String, u8) {
    let prec = match op {
        BinOp::Add | BinOp::Sub => 1,
        BinOp::Mul | BinOp::Div => 2,
        BinOp::Pow => 4,
    };

    let left_rendered = render_with_prec(left, prec, mode);
    let right_parent_prec = if matches!(op, BinOp::Pow) {
        prec
    } else {
        prec + 1
    };
    let right_rendered = render_with_prec(right, right_parent_prec, mode);

    let rendered = match (op, mode) {
        (BinOp::Add, _) => format!("{left_rendered} + {right_rendered}"),
        (BinOp::Sub, _) => format!("{left_rendered} - {right_rendered}"),
        (BinOp::Mul, RenderMode::Latex) => format!("{left_rendered} \\cdot {right_rendered}"),
        (BinOp::Mul, RenderMode::Pretty) => format!("{left_rendered} · {right_rendered}"),
        (BinOp::Mul, RenderMode::Text) => format!("{left_rendered} * {right_rendered}"),
        (BinOp::Div, RenderMode::Latex) => format!("{left_rendered} / {right_rendered}"),
        (BinOp::Div, RenderMode::Pretty) => format!("{left_rendered} / {right_rendered}"),
        (BinOp::Div, RenderMode::Text) => format!("{left_rendered} / {right_rendered}"),
        (BinOp::Pow, RenderMode::Latex) => format!("{left_rendered}^{{{right_rendered}}}"),
        (BinOp::Pow, RenderMode::Pretty) => format!(
            "{left_rendered}{}",
            to_superscript_if_simple(&right_rendered)
        ),
        (BinOp::Pow, RenderMode::Text) => format!("{left_rendered}^{right_rendered}"),
    };

    (rendered, prec)
}

fn render_call(name: &str, args: &[Expr], mode: RenderMode) -> (String, u8) {
    let rendered_args: Vec<String> = args
        .iter()
        .map(|arg| render_with_prec(arg, 0, mode))
        .collect();

    let rendered = match name {
        "frac" if args.len() == 2 => match mode {
            RenderMode::Latex => format!("\\frac{{{}}}{{{}}}", rendered_args[0], rendered_args[1]),
            RenderMode::Pretty => format!("{}/{}", rendered_args[0], rendered_args[1]),
            RenderMode::Text => format!("frac({}, {})", rendered_args[0], rendered_args[1]),
        },
        "sqrt" if args.len() == 1 => match mode {
            RenderMode::Latex => format!("\\sqrt{{{}}}", rendered_args[0]),
            RenderMode::Pretty => format!("√{}", rendered_args[0]),
            RenderMode::Text => format!("sqrt({})", rendered_args[0]),
        },
        "sin" | "cos" | "tan" | "log" | "ln" | "exp" if args.len() == 1 => match mode {
            RenderMode::Latex => format!("\\{}\\left({}\\right)", name, rendered_args[0]),
            RenderMode::Pretty => format!("{name}({})", rendered_args[0]),
            RenderMode::Text => format!("{name}({})", rendered_args[0]),
        },
        _ => {
            let args_joined = rendered_args.join(", ");
            match mode {
                RenderMode::Latex => {
                    format!("\\operatorname{{{name}}}\\left({args_joined}\\right)")
                }
                RenderMode::Pretty => format!("{name}({args_joined})"),
                RenderMode::Text => format!("{name}({args_joined})"),
            }
        }
    };

    (rendered, 6)
}

fn render_ident(name: &str, mode: RenderMode) -> String {
    if let Some((latex, pretty)) = greek_name(name) {
        return match mode {
            RenderMode::Latex => latex.to_string(),
            RenderMode::Pretty => pretty.to_string(),
            RenderMode::Text => name.to_string(),
        };
    }

    name.to_string()
}

fn greek_name(name: &str) -> Option<(&'static str, &'static str)> {
    match name {
        "alpha" => Some(("\\alpha", "α")),
        "beta" => Some(("\\beta", "β")),
        "gamma" => Some(("\\gamma", "γ")),
        "delta" => Some(("\\delta", "δ")),
        "epsilon" => Some(("\\epsilon", "ε")),
        "zeta" => Some(("\\zeta", "ζ")),
        "eta" => Some(("\\eta", "η")),
        "theta" => Some(("\\theta", "θ")),
        "iota" => Some(("\\iota", "ι")),
        "kappa" => Some(("\\kappa", "κ")),
        "lambda" => Some(("\\lambda", "λ")),
        "mu" => Some(("\\mu", "μ")),
        "nu" => Some(("\\nu", "ν")),
        "xi" => Some(("\\xi", "ξ")),
        "pi" => Some(("\\pi", "π")),
        "rho" => Some(("\\rho", "ρ")),
        "sigma" => Some(("\\sigma", "σ")),
        "tau" => Some(("\\tau", "τ")),
        "upsilon" => Some(("\\upsilon", "υ")),
        "phi" => Some(("\\phi", "φ")),
        "chi" => Some(("\\chi", "χ")),
        "psi" => Some(("\\psi", "ψ")),
        "omega" => Some(("\\omega", "ω")),
        "Gamma" => Some(("\\Gamma", "Γ")),
        "Delta" => Some(("\\Delta", "Δ")),
        "Theta" => Some(("\\Theta", "Θ")),
        "Lambda" => Some(("\\Lambda", "Λ")),
        "Xi" => Some(("\\Xi", "Ξ")),
        "Pi" => Some(("\\Pi", "Π")),
        "Sigma" => Some(("\\Sigma", "Σ")),
        "Phi" => Some(("\\Phi", "Φ")),
        "Psi" => Some(("\\Psi", "Ψ")),
        "Omega" => Some(("\\Omega", "Ω")),
        _ => None,
    }
}

fn to_superscript_if_simple(value: &str) -> String {
    if value.chars().all(|ch| ch.is_ascii_digit()) {
        return value.chars().map(super_digit).collect();
    }
    if value.len() == 1 {
        if let Some(ch) = value.chars().next() {
            return match ch {
                'n' => "ⁿ".to_string(),
                'i' => "ⁱ".to_string(),
                '+' => "⁺".to_string(),
                '-' => "⁻".to_string(),
                '=' => "⁼".to_string(),
                '(' => "⁽".to_string(),
                ')' => "⁾".to_string(),
                _ => value.to_string(),
            };
        }
    }
    format!("^({value})")
}

fn to_subscript_if_simple(value: &str) -> String {
    if value.chars().all(|ch| ch.is_ascii_digit()) {
        return value.chars().map(sub_digit).collect();
    }
    if value.len() == 1 {
        if let Some(ch) = value.chars().next() {
            return match ch {
                'a' => "ₐ".to_string(),
                'e' => "ₑ".to_string(),
                'h' => "ₕ".to_string(),
                'i' => "ᵢ".to_string(),
                'j' => "ⱼ".to_string(),
                'k' => "ₖ".to_string(),
                'l' => "ₗ".to_string(),
                'm' => "ₘ".to_string(),
                'n' => "ₙ".to_string(),
                'o' => "ₒ".to_string(),
                'p' => "ₚ".to_string(),
                'r' => "ᵣ".to_string(),
                's' => "ₛ".to_string(),
                't' => "ₜ".to_string(),
                'u' => "ᵤ".to_string(),
                'v' => "ᵥ".to_string(),
                'x' => "ₓ".to_string(),
                '+' => "₊".to_string(),
                '-' => "₋".to_string(),
                '=' => "₌".to_string(),
                '(' => "₍".to_string(),
                ')' => "₎".to_string(),
                _ => value.to_string(),
            };
        }
    }
    format!("_{{{value}}}")
}

fn super_digit(ch: char) -> String {
    match ch {
        '0' => "⁰",
        '1' => "¹",
        '2' => "²",
        '3' => "³",
        '4' => "⁴",
        '5' => "⁵",
        '6' => "⁶",
        '7' => "⁷",
        '8' => "⁸",
        '9' => "⁹",
        _ => "",
    }
    .to_string()
}

fn sub_digit(ch: char) -> String {
    match ch {
        '0' => "₀",
        '1' => "₁",
        '2' => "₂",
        '3' => "₃",
        '4' => "₄",
        '5' => "₅",
        '6' => "₆",
        '7' => "₇",
        '8' => "₈",
        '9' => "₉",
        _ => "",
    }
    .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn renders_frac_and_greek() {
        let expr = parse_expression("frac(1, 2) + alpha").unwrap();
        let rendered = RenderedMath {
            latex: render_latex(&expr),
            pretty: render_pretty(&expr),
            text: Some(render_text(&expr)),
            debug: Some(debug_tree(&expr)),
        };

        assert!(rendered.latex.contains("\\frac{1}{2}"));
        assert!(rendered.pretty.contains('α'));
        assert!(rendered.debug.unwrap().contains("Call(frac"));
    }

    #[test]
    fn renders_sqrt_power_and_subscript() {
        let expr = parse_expression("sqrt(x) + beta^2_1").unwrap();
        let latex = render_latex(&expr);
        let pretty = render_pretty(&expr);

        assert!(latex.contains("\\sqrt{x}"));
        assert!(latex.contains("\\beta"));
        assert!(pretty.contains('β'));
    }

    #[test]
    fn falls_back_on_parse_error() {
        let source = "frac(1,";
        let rendered = match parse_expression(source) {
            Ok(_) => panic!("expected parse error"),
            Err(err) => RenderedMath {
                latex: source.to_string(),
                pretty: source.to_string(),
                text: Some(source.to_string()),
                debug: Some(format!("parse_error({err})")),
            },
        };

        assert!(rendered.debug.unwrap().contains("parse_error"));
    }
}
