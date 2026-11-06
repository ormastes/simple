//! Distinguish nested error propagation from the separate `?.` operator.
use simple_compiler::interpreter;
use simple_parser::{ast::{Expr, Node}, Parser};

fn constructor_payload(source: &str) -> Expr {
    let module = Parser::new(source).parse().expect("constructor expression parses");
    let Node::Expression(Expr::Call { args, .. }) = &module.items[0] else {
        panic!("expected a constructor call expression");
    };
    args[0].value.clone()
}

#[test]
fn question_dot_is_optional_chain_not_try() {
    let payload = constructor_payload("Ok(pool.row(7)?.op)\n");
    assert!(matches!(payload, Expr::OptionalChain { field, .. } if field == "op"));

    let payload = constructor_payload("Ok((pool.row(7)?).op)\n");
    assert!(matches!(payload, Expr::FieldAccess { receiver, field }
        if field == "op" && matches!(receiver.as_ref(), Expr::Try(_))));
}

const SOURCE: &str = r#"
struct Row:
    op: i64

class Pool:
    fn row(self, node: i64) -> Result<Row, text>:
        if node != 7:
            return Err("no row")
        Ok(Row(op: 23))

    fn propagated_op(self, node: i64) -> Result<i64, text>:
        Ok((self.row(node)?).op)

    fn propagated_payload(self, node: i64) -> Result<Row, text>:
        Ok(self.row(node)?)

    fn optional_op(self, node: i64) -> Result<i64, text>:
        Ok(self.row(node)?.op ?? -1)

fn main() -> i64:
    val pool = Pool()
    match pool.propagated_op(999999):
        case Err(error):
            if error != "no row": return 1
        case _: return 2
    match pool.propagated_op(7):
        case Ok(value):
            if value != 23: return 3
        case _: return 4
    match pool.propagated_payload(999999):
        case Err(error):
            if error != "no row": return 5
        case _: return 6
    match pool.propagated_payload(7):
        case Ok(row):
            if row.op != 23: return 7
        case _: return 8
    match pool.optional_op(999999):
        case Ok(value):
            if value != -1: return 9
        case _: return 10
    match pool.optional_op(7):
        case Ok(value):
            if value != 23: return 11
        case _: return 12
    return 0
"#;

#[test]
fn nested_try_propagates_from_constructor_arguments_but_optional_chain_does_not() {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let source = format!("{SOURCE}\nmain = main()\n");
    let module = Parser::new(&source).parse().expect("nested try fixture parses");
    let result = interpreter::evaluate_module(&module.items).expect("nested try fixture executes");
    assert_eq!(result, 0, "nested try/optional-chain distinction failed at case {result}");
}
