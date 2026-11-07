use simple_parser::{Parser, ast::{AssignOp, BinOp, Expr, FunctionDef, MatchStmt, Node, Pattern}};

fn require(ok: bool, message: &str) -> Result<(), String> {
    if ok { Ok(()) } else { Err(message.to_owned()) }
}
fn function(source: &str) -> Result<FunctionDef, String> {
    let module = Parser::new(source).parse().map_err(|e| format!("parse: {e}"))?;
    match module.items.into_iter().next() {
        Some(Node::Function(def)) => Ok(def),
        other => Err(format!("expected first function, found {other:?}")),
    }
}
fn match_body(source: &str, count: usize) -> Result<MatchStmt, String> {
    let def = function(source)?;
    require(def.body.statements.len() == 1, "match function must contain exactly one statement")?;
    match def.body.statements.into_iter().next() {
        Some(Node::Match(stmt)) => {
            require(stmt.arms.len() == count, "arm count changed or next arm was swallowed")?;
            require(stmt.arms.iter().all(|arm| arm.body.statements.len() == 1), "arm body statement count changed")?;
            Ok(stmt)
        }
        other => Err(format!("expected match statement, found {other:?}")),
    }
}
fn readme() -> Result<(), String> {
    let stmt = match_body(include_str!("fixtures/match_arrow_arms/readme_arrow.spl"), 4)?;
    for (arm, (variant, arity, operator)) in stmt.arms.iter().zip([
        ("Circle", 1, BinOp::Mul), ("Rectangle", 2, BinOp::Mul),
        ("Square", 1, BinOp::Mul), ("Triangle", 3, BinOp::Add),
    ]) {
        require(matches!(&arm.pattern, Pattern::Enum { variant: name, payload: Some(values), .. } if name == variant && values.len() == arity), "README constructor pattern/arity changed")?;
        require(arm.guard.is_none(), "README unguarded arm gained a guard")?;
        require(matches!(&arm.body.statements[0], Node::Expression(Expr::Binary { op, .. }) if *op == operator), "README arm expression became a signature/lambda or wrong binary expression")?;
    }
    Ok(())
}
fn literal_arrows() -> Result<(), String> {
    let stmt = match_body(include_str!("fixtures/match_arrow_arms/literal_arrows.spl"), 3)?;
    require(matches!(&stmt.arms[0].pattern, Pattern::Literal(value) if matches!(value.as_ref(), Expr::Integer(0))), "literal zero pattern changed")?;
    require(matches!(&stmt.arms[1].pattern, Pattern::Literal(value) if matches!(value.as_ref(), Expr::Integer(1))), "literal one pattern changed")?;
    require(matches!(&stmt.arms[2].pattern, Pattern::Wildcard), "wildcard pattern changed")?;
    for (arm, expected) in stmt.arms.iter().zip(["zero", "one", "other"]) {
        require(matches!(&arm.body.statements[0], Node::Expression(Expr::String(value)) if value == expected), "literal arrow body changed")?;
    }
    Ok(())
}
fn guarded_arrows() -> Result<(), String> {
    let stmt = match_body(include_str!("fixtures/match_arrow_arms/guarded_arrows.spl"), 2)?;
    require(matches!(&stmt.arms[0].pattern, Pattern::Identifier(name) if name == "n"), "guard subject binding changed")?;
    require(matches!(&stmt.arms[0].guard, Some(Expr::Binary { op: BinOp::Lt, .. })), "guard comparison missing")?;
    require(matches!(&stmt.arms[1].pattern, Pattern::Wildcard) && stmt.arms[1].guard.is_none(), "fallback guard/pattern changed")
}
fn qualified_arrows() -> Result<(), String> {
    let stmt = match_body(include_str!("fixtures/match_arrow_arms/qualified_arrows.spl"), 2)?;
    for (arm, expected) in stmt.arms.iter().zip(["Circle", "Square"]) {
        require(matches!(&arm.pattern, Pattern::Enum { name, variant, payload: Some(values) } if name == "Shape" && variant == expected && values.len() == 1), "qualified enum owner/payload lost")?;
        require(matches!(&arm.body.statements[0], Node::Expression(Expr::Identifier(_))), "qualified arm body changed")?;
    }
    Ok(())
}

#[test]
fn original_readme_arrow_arm_expressions() -> Result<(), String> { readme() }
#[test]
fn literal_arrow_arms_keep_separate_bodies() -> Result<(), String> { literal_arrows() }
#[test]
fn guarded_arrow_arms_keep_their_guard() -> Result<(), String> { guarded_arrows() }
#[test]
fn qualified_arrow_arms_keep_owner_and_payload() -> Result<(), String> { qualified_arrows() }

#[test]
fn bitwise_or_outside_match_and_on_arm_line_is_unchanged() -> Result<(), String> {
    let def = function("fn bits() -> i64:\n    1\n        | 2\n")?;
    require(matches!(&def.body.statements[..], [Node::Expression(Expr::Binary { op: BinOp::BitOr, .. })]), "outside-match leading BitOr changed")?;
    let stmt = match_body("fn bits(value: i64) -> i64:\n    match value:\n        | 0 -> 1 | 2\n        | _ -> 0\n", 2)?;
    require(matches!(&stmt.arms[0].body.statements[..], [Node::Expression(Expr::Binary { op: BinOp::BitOr, .. })]), "same-line arm BitOr changed")
}

#[test]
fn deeper_bitwise_or_stays_inside_an_arm() -> Result<(), String> {
    let stmt = match_body("fn bits(value: i64) -> i64:\n    match value:\n        | 0 -> 1\n            | 2\n        | _ -> 0\n", 2)?;
    require(matches!(&stmt.arms[0].body.statements[..], [Node::Expression(Expr::Binary { op: BinOp::BitOr, .. })]), "deeper leading BitOr became an arm")
}

#[test]
fn nested_statement_and_expression_matches_restore_arm_boundaries() -> Result<(), String> {
    let stmt = match_body("fn nested(value: i64) -> i64:\n    match value:\n        | 0 -> match value:\n            | 1 -> 2\n            | _ -> 3\n        | _ -> 4\n", 2)?;
    require(matches!(&stmt.arms[0].body.statements[..], [Node::Match(inner)] if inner.arms.len() == 2), "nested statement match lost its arms")?;
    let def = function("fn nested(value: i64) -> i64:\n    val result = match value:\n        | 0 -> 1\n        | _ -> 2\n    result\n")?;
    require(matches!(&def.body.statements[0], Node::Let(binding) if matches!(&binding.value, Some(Expr::Match { arms, .. }) if arms.len() == 2)), "expression match consumed the next arm")
}
