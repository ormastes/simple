//! Freestanding module-global runtime initializer synthesis.
//!
//! Hosted builds intentionally never call this pass.  Native heap-backed
//! constants already have backend-specific initialization, but arbitrary
//! module expressions (constructor calls in particular) need to travel through
//! normal HIR/MIR lowering so their result can be stored in global storage.

use simple_parser::ast::{
    AssignOp, AssignmentStmt, Block, Expr, FunctionDef, Module, Node, Pattern, ReturnStmt, Type, Visibility,
};
use simple_parser::token::Span;

fn pattern_name(pattern: &Pattern) -> Option<&str> {
    match pattern {
        Pattern::Identifier(name) | Pattern::MutIdentifier(name) | Pattern::MoveIdentifier(name) => Some(name),
        Pattern::Typed { pattern, .. } => pattern_name(pattern),
        _ => None,
    }
}

fn pattern_type(pattern: &Pattern) -> Option<&Type> {
    match pattern {
        Pattern::Typed { ty, .. } => Some(ty),
        _ => None,
    }
}

fn is_const_integer_expr(expr: &Expr) -> bool {
    match expr {
        Expr::Integer(_) | Expr::TypedInteger(_, _) => true,
        Expr::Unary { op, operand } => {
            matches!(
                op,
                simple_parser::ast::UnaryOp::Neg | simple_parser::ast::UnaryOp::BitNot
            ) && is_const_integer_expr(operand)
        }
        Expr::Binary { op, left, right } => {
            matches!(
                op,
                simple_parser::ast::BinOp::Add
                    | simple_parser::ast::BinOp::Sub
                    | simple_parser::ast::BinOp::Mul
                    | simple_parser::ast::BinOp::Div
                    | simple_parser::ast::BinOp::Mod
                    | simple_parser::ast::BinOp::BitAnd
                    | simple_parser::ast::BinOp::BitOr
                    | simple_parser::ast::BinOp::BitXor
                    | simple_parser::ast::BinOp::ShiftLeft
                    | simple_parser::ast::BinOp::ShiftRight
            ) && is_const_integer_expr(left)
                && is_const_integer_expr(right)
        }
        _ => false,
    }
}

fn is_const_float_expr(expr: &Expr) -> bool {
    match expr {
        Expr::Float(_) | Expr::TypedFloat(_, _) | Expr::Integer(_) | Expr::TypedInteger(_, _) => true,
        Expr::Unary {
            op: simple_parser::ast::UnaryOp::Neg,
            operand,
        } => is_const_float_expr(operand),
        Expr::Binary { op, left, right } => {
            matches!(
                op,
                simple_parser::ast::BinOp::Add
                    | simple_parser::ast::BinOp::Sub
                    | simple_parser::ast::BinOp::Mul
                    | simple_parser::ast::BinOp::Div
            ) && is_const_float_expr(left)
                && is_const_float_expr(right)
        }
        _ => false,
    }
}

fn is_literal_fstring(expr: &Expr) -> bool {
    match expr {
        Expr::FString { parts, .. } => {
            parts.is_empty()
                || (parts.len() == 1 && matches!(parts.first(), Some(simple_parser::ast::FStringPart::Literal(_))))
        }
        _ => false,
    }
}

fn is_const_array_element(expr: &Expr) -> bool {
    matches!(expr, Expr::Bool(_)) || is_const_integer_expr(expr)
}

fn is_simple_struct_field_value(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Integer(_) | Expr::Bool(_) | Expr::Nil | Expr::Float(_) | Expr::String(_)
    ) || matches!(expr, Expr::Array(elements) if elements.is_empty())
}

fn declared_type_name(ty: Option<&Type>) -> Option<&str> {
    match ty {
        Some(Type::Simple(name)) | Some(Type::Generic { name, .. }) => Some(name),
        _ => None,
    }
}

fn is_optional_function_call(expr: &Expr, declared_type: Option<&Type>) -> bool {
    matches!(declared_type, Some(Type::Optional(_))) && matches!(expr, Expr::Call { .. })
}

/// True when the existing global metadata/codegen path already preserves the
/// initializer without lowering an executable assignment.
fn already_initialized_without_runtime_assignment(expr: &Expr, declared_type: Option<&Type>) -> bool {
    match expr {
        Expr::Integer(_)
        | Expr::TypedInteger(_, _)
        | Expr::Float(_)
        | Expr::TypedFloat(_, _)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::String(_) => true,
        Expr::FString { .. } => is_literal_fstring(expr),
        Expr::Unary { .. } | Expr::Binary { .. } => is_const_integer_expr(expr) || is_const_float_expr(expr),
        Expr::Array(elements) => elements.iter().all(is_const_array_element),
        Expr::ArrayRepeat { value, count } => is_const_array_element(value) && is_const_integer_expr(count),
        Expr::StructInit { fields, spread, .. } => {
            spread.is_none() && fields.iter().all(|(_, value)| is_simple_struct_field_value(value))
        }
        Expr::Call { callee, args } => {
            let constructor_name = match callee.as_ref() {
                Expr::Identifier(name) => Some(name.as_str()),
                _ => None,
            };
            constructor_name == declared_type_name(declared_type)
                && args
                    .iter()
                    .all(|arg| arg.name.is_some() && is_simple_struct_field_value(&arg.value))
        }
        _ => false,
    }
}

fn sanitized_component(raw: &str) -> String {
    let mut result = String::with_capacity(raw.len());
    for ch in raw.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            result.push(ch);
        } else {
            result.push('_');
        }
    }
    if result.is_empty() {
        "module".to_string()
    } else {
        result
    }
}

fn runtime_init_function(name: String, statements: Vec<Node>, span: Span) -> Node {
    let mut statements = statements;
    statements.push(Node::Return(ReturnStmt { span, value: None }));
    Node::Function(FunctionDef {
        span,
        name,
        generic_params: Vec::new(),
        params: Vec::new(),
        return_type: Some(Type::Simple("void".to_string())),
        where_clause: Vec::new(),
        body: Block { span, statements },
        visibility: Visibility::Private,
        effects: Vec::new(),
        decorators: Vec::new(),
        attributes: Vec::new(),
        doc_comment: None,
        contract: None,
        is_abstract: false,
        is_sync: true,
        bounds_block: None,
        is_static: false,
        is_me_method: false,
        is_generator: false,
        return_constraint: None,
        is_generic_template: false,
        specialization_of: None,
        type_bindings: std::collections::HashMap::new(),
    })
}

/// Append compiler-reserved module initializers for values that cannot be
/// represented as static global metadata. Optional function-call globals get
/// one declaration-indexed initializer each so no same-shaped declaration can
/// be collapsed or skipped by the freestanding module-init symbol pipeline.
pub(super) fn inject_freestanding_module_global_init(module: &mut Module, module_prefix: &str) {
    let span = Span::new(0, 0, 0, 0);
    let mut statements = Vec::new();
    let mut optional_call_initializers = Vec::new();

    for (declaration_index, item) in module.items.iter_mut().enumerate() {
        let candidate = match item {
            Node::Static(stmt) => Some((stmt.name.as_str(), &mut stmt.value, stmt.ty.as_ref())),
            Node::Const(stmt) => Some((stmt.name.as_str(), &mut stmt.value, stmt.ty.as_ref())),
            Node::Let(stmt) => stmt.value.as_mut().and_then(|value| {
                pattern_name(&stmt.pattern)
                    .map(|name| (name, value, stmt.ty.as_ref().or_else(|| pattern_type(&stmt.pattern))))
            }),
            _ => None,
        };
        let Some((name, value, declared_type)) = candidate else {
            continue;
        };
        if already_initialized_without_runtime_assignment(value, declared_type) {
            continue;
        }
        let assignment = Node::Assignment(AssignmentStmt {
            span,
            target: Expr::Identifier(name.to_string()),
            op: AssignOp::Assign,
            value: value.clone(),
        });
        if is_optional_function_call(value, declared_type) {
            // Freestanding global storage otherwise starts as raw zero. Keep
            // the slot a valid Optional even before its eager initializer runs.
            *value = Expr::Nil;
            optional_call_initializers.push((declaration_index, assignment));
        } else {
            statements.push(assignment);
        }
    }

    let prefix = sanitized_component(module_prefix);
    if !statements.is_empty() {
        module.items.push(runtime_init_function(
            format!("__module_init_{}_dynamic", prefix),
            statements,
            span,
        ));
    }
    for (declaration_index, assignment) in optional_call_initializers {
        module.items.push(runtime_init_function(
            format!("__module_init_{}_dynamic_optional_{declaration_index:08}", prefix),
            vec![assignment],
            span,
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::Parser;

    #[test]
    fn synthesizes_declaration_order_assignments_for_runtime_initializers_only() {
        let source = "val literal: i64 = 7\nval first = make_first()\nval second = make_second(first)\n";
        let mut module = Parser::new(source).parse().expect("parse module globals");
        inject_freestanding_module_global_init(&mut module, "app__globals");

        let init = module
            .items
            .iter()
            .find_map(|item| match item {
                Node::Function(function) if function.name.starts_with("__module_init_") => Some(function),
                _ => None,
            })
            .expect("runtime initializer");
        assert_eq!(init.name, "__module_init_app__globals_dynamic");
        let targets: Vec<&str> = init
            .body
            .statements
            .iter()
            .filter_map(|item| match item {
                Node::Assignment(AssignmentStmt {
                    target: Expr::Identifier(name),
                    ..
                }) => Some(name.as_str()),
                _ => None,
            })
            .collect();
        assert_eq!(targets, vec!["first", "second"]);
    }

    #[test]
    fn synthesizes_every_optional_call_global_in_declaration_order() {
        let source = "struct Mutex:\n    value: i64\nfn mutex_new(value: i64) -> Mutex:\n    Mutex(value: value)\nvar first: Mutex? = mutex_new(0)\nfn between():\n    return\nvar second: Mutex? = mutex_new(0)\n";
        let mut module = Parser::new(source).parse().expect("parse optional call globals");
        inject_freestanding_module_global_init(&mut module, "font_renderer");

        let initializers: Vec<(&str, &str)> = module
            .items
            .iter()
            .filter_map(|item| match item {
                Node::Function(function) if function.name.contains("_dynamic_optional_") => {
                    let target = function.body.statements.iter().find_map(|statement| match statement {
                        Node::Assignment(AssignmentStmt {
                            target: Expr::Identifier(name),
                            ..
                        }) => Some(name.as_str()),
                        _ => None,
                    })?;
                    Some((function.name.as_str(), target))
                }
                _ => None,
            })
            .collect();
        assert_eq!(
            initializers,
            vec![
                ("__module_init_font_renderer_dynamic_optional_00000002", "first"),
                ("__module_init_font_renderer_dynamic_optional_00000004", "second"),
            ]
        );

        let seeded_nil: Vec<&str> = module
            .items
            .iter()
            .filter_map(|item| match item {
                Node::Let(stmt) if matches!(stmt.value, Some(Expr::Nil)) => pattern_name(&stmt.pattern),
                _ => None,
            })
            .collect();
        assert_eq!(seeded_nil, vec!["first", "second"]);
    }

    #[test]
    fn omits_initializer_when_all_globals_are_statically_representable() {
        let source = "val integer: i64 = 7\nval message: text = \"ready\"\nval values = [1, 2, 3]\n";
        let mut module = Parser::new(source).parse().expect("parse literals");
        inject_freestanding_module_global_init(&mut module, "literal_module");
        assert!(!module
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(function) if function.name.starts_with("__module_init_"))));
    }

    #[test]
    fn comparison_is_runtime_but_simple_struct_metadata_is_not_duplicated() {
        let comparison = Expr::Binary {
            op: simple_parser::ast::BinOp::Lt,
            left: Box::new(Expr::Integer(1)),
            right: Box::new(Expr::Integer(2)),
        };
        assert!(!already_initialized_without_runtime_assignment(&comparison, None));

        let constructor = Expr::Call {
            callee: Box::new(Expr::Identifier("Config".to_string())),
            args: vec![simple_parser::ast::Argument {
                name: Some("value".to_string()),
                value: Expr::Integer(1),
                span: Span::new(0, 0, 0, 0),
                label: None,
            }],
        };
        assert!(already_initialized_without_runtime_assignment(
            &constructor,
            Some(&Type::Simple("Config".to_string()))
        ));
    }
}
