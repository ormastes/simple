use simple_parser::{Parser, ast::{Expr, FunctionDef, Node}};

fn require(ok: bool, message: &str) -> Result<(), String> {
    if ok { Ok(()) } else { Err(message.to_owned()) }
}
fn argument<'a>(expr: &'a Expr, name: &str) -> Result<&'a Expr, String> {
    match expr {
        Expr::Call { callee, args } if matches!(callee.as_ref(), Expr::Identifier(n) if n == name) && args.len() == 1 => Ok(&args[0].value),
        other => Err(format!("expected {name} with one argument, got {other:?}")),
    }
}
fn check(source: &str, assigned: bool, nested: bool, matching: bool) -> Result<(), String> {
    let module = Parser::new(source).parse().map_err(|error| format!("{error:?}"))?;
    require(module.items.len() == 2, "delimiter swallowed or prematurely closed a top-level function")?;
    let install: &FunctionDef = match &module.items[0] {
        Node::Function(def) if def.name == "install" => def,
        other => return Err(format!("install function missing: {other:?}")),
    };
    require(matches!(&module.items[1], Node::Function(def) if def.name == "after" && matches!(&def.body.statements[..], [Node::Expression(Expr::Integer(7))])), "following function/body changed")?;
    require(install.body.statements.len() == if assigned || nested { 2 } else { 1 }, "lambda stole or leaked its enclosing function block")?;
    let lambda = if assigned {
        match &install.body.statements[0] {
            Node::Let(binding) => binding.value.as_ref().ok_or("assigned lambda missing")?,
            other => return Err(format!("assigned lambda binding changed: {other:?}")),
        }
    } else {
        let expression = match &install.body.statements[0] {
            Node::Expression(expr) => expr,
            other => return Err(format!("registration call changed: {other:?}")),
        };
        let registration = if nested { argument(expression, "wrap")? } else { expression };
        argument(registration, "registry_register")?
    };
    let body = match lambda {
        Expr::Lambda { params, body, .. } if params.len() == 1 => match body.as_ref() {
            Expr::DoBlock(body) => body,
            other => return Err(format!("lambda block changed: {other:?}")),
        },
        other => return Err(format!("lambda lost: {other:?}")),
    };
    if matching {
        let stmt = match &body[..] {
            [Node::Match(stmt)] => stmt,
            other => return Err(format!("nested match/body changed: {other:?}")),
        };
        require(stmt.arms.len() == 2, "last match arm was swallowed")?;
        require(matches!(argument(&stmt.subject, "handler")?, Expr::Identifier(name) if name == "args"), "match subject argument changed")?;
        for (arm, expected) in stmt.arms.iter().zip(["value", "reason"]) {
            require(matches!(&arm.body.statements[..], [Node::Expression(Expr::Identifier(name))] if name == expected), "match arm expression changed")?;
        }
    } else {
        require(matches!(&body[..], [Node::Expression(Expr::Identifier(name))] if name == "args"), "simple lambda body changed")?;
    }
    if assigned {
        let expr = match &install.body.statements[1] { Node::Expression(expr) => expr, _ => return Err("assigned callback call missing".into()) };
        require(matches!(argument(expr, "registry_register")?, Expr::Identifier(name) if name == "callback"), "assigned callback registration changed")?;
    }
    if nested {
        require(matches!(&install.body.statements[1], Node::Let(binding) if matches!(&binding.value, Some(Expr::Integer(7)))), "outer function tail binding changed")?;
    }
    Ok(())
}
#[test]
fn anonymous_fn_same_line_closer() -> Result<(), String> {
    check(include_str!("fixtures/anonymous_fn_closer/simple_lambda_call.spl"), false, false, false)
}
#[test]
fn anonymous_fn_nested_match_same_line_closer() -> Result<(), String> {
    check(include_str!("fixtures/anonymous_fn_closer/nested_match_call.spl"), false, false, true)
}
#[test]
fn assigned_anonymous_fn_nested_match() -> Result<(), String> {
    check(include_str!("fixtures/anonymous_fn_closer/assigned_nested_match.spl"), true, false, true)
}
#[test]
fn anonymous_fn_nested_match_separate_closer() -> Result<(), String> {
    check(include_str!("fixtures/anonymous_fn_closer/separate_closing_paren.spl"), false, false, true)
}
#[test]
fn anonymous_fn_nested_enclosing_calls_keep_outer_tail() -> Result<(), String> {
    check(include_str!("fixtures/anonymous_fn_closer/nested_enclosing_calls.spl"), false, true, true)
}
