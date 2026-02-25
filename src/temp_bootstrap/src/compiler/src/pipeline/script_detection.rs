//! Script vs module detection utilities.

use simple_parser::ast::{self, Node};
use simple_parser::token::Span;

/// Detect whether the module contains script-style statements (non-item code) at the top level.
///
/// These should be interpreted directly rather than lowered through HIR/MIR.
pub fn has_script_statements(items: &[Node]) -> bool {
    use Node::*;
    items.iter().any(|item| {
        matches!(
            item,
            Let(_)
                | Const(_)
                | Static(_)
                | Assignment(_)
                | Return(_)
                | If(_)
                | Match(_)
                | For(_)
                | While(_)
                | Loop(_)
                | Break(_)
                | Continue(_)
                | Context(_)
                | With(_)
                | Expression(_)
        )
    })
}

/// Wrap script-style statements in an implicit `fn main() -> i64:` function.
///
/// This transforms a module like:
/// ```simple
/// val x = 42
/// print(x)
/// main = x
/// ```
/// Into:
/// ```simple
/// fn main() -> i64:
///     val x = 42
///     print(x)
///     return x
/// ```
///
/// Non-statement items (functions, structs, etc.) are kept at module level.
/// The last `main = <expr>` assignment, if present, becomes the return value.
pub fn wrap_script_as_main(module: &mut ast::Module) {
    let span = Span::new(0, 0, 0, 0);

    let mut declarations = Vec::new();
    let mut script_stmts = Vec::new();

    for item in module.items.drain(..) {
        if is_declaration(&item) {
            declarations.push(item);
        } else {
            script_stmts.push(item);
        }
    }

    // If no script statements, nothing to wrap
    if script_stmts.is_empty() {
        module.items = declarations;
        return;
    }

    // Check if there's a `main = <expr>` assignment and convert it to a return
    let has_main_assignment = script_stmts.iter().any(|item| {
        if let Node::Assignment(assign) = item {
            if let ast::Expr::Identifier(name) = &assign.target {
                return name == "main";
            }
        }
        false
    });

    // Transform: replace `main = expr` with `return expr`
    let body_stmts: Vec<Node> = script_stmts
        .into_iter()
        .map(|item| {
            if let Node::Assignment(assign) = &item {
                if let ast::Expr::Identifier(name) = &assign.target {
                    if name == "main" {
                        return Node::Return(ast::ReturnStmt {
                            span: assign.span.clone(),
                            value: Some(assign.value.clone()),
                        });
                    }
                }
            }
            item
        })
        .collect();

    // If there's no main assignment, add a `return 0` at the end
    let mut final_stmts = body_stmts;
    if !has_main_assignment {
        final_stmts.push(Node::Return(ast::ReturnStmt {
            span: span.clone(),
            value: Some(ast::Expr::Integer(0)),
        }));
    }

    let main_fn = Node::Function(ast::FunctionDef {
        span: span.clone(),
        name: "main".to_string(),
        generic_params: Vec::new(),
        params: Vec::new(),
        return_type: Some(ast::Type::Simple("i64".to_string())),
        where_clause: ast::WhereClause::default(),
        body: ast::Block {
            span: span.clone(),
            statements: final_stmts,
        },
        visibility: ast::Visibility::Public,
        effect: None,
        decorators: Vec::new(),
        attributes: Vec::new(),
        doc_comment: None,
        contract: None,
        is_abstract: false,
    });

    // Declarations first, then the synthetic main function
    declarations.push(main_fn);
    module.items = declarations;
}

/// Check if a node is a declaration (not a script-style statement).
fn is_declaration(node: &Node) -> bool {
    use Node::*;
    matches!(
        node,
        Function(_)
            | Struct(_)
            | Class(_)
            | Enum(_)
            | Trait(_)
            | Impl(_)
            | Actor(_)
            | TypeAlias(_)
            | Extern(_)
            | Macro(_)
            | Unit(_)
            | UnitFamily(_)
            | ModDecl(_)
            | UseStmt(_)
            | CommonUseStmt(_)
            | ExportUseStmt(_)
            | AutoImportStmt(_)
    )
}
