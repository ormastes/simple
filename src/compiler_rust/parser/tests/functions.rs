use simple_parser::ast::{Expr, Node, Type};
use simple_parser::Parser;

fn parse(src: &str) -> Vec<Node> {
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("parse ok");
    module.items
}

fn parse_ok(src: &str) {
    let mut parser = Parser::new(src);
    parser.parse().expect("should parse");
}

// Function definitions
#[test]
fn parse_function_definition() {
    let items = parse("fn add(a, b):\n    return a + b");
    if let Node::Function(f) = &items[0] {
        assert_eq!(f.name, "add");
        assert_eq!(f.params.len(), 2);
    } else {
        panic!("expected function");
    }
}

#[test]
fn parse_function_with_return_type() {
    let items = parse("fn add(a: i64, b: i64) -> i64:\n    return a + b");
    if let Node::Function(f) = &items[0] {
        assert!(f.return_type.is_some());
    } else {
        panic!("expected function");
    }
}

#[test]
fn parse_function_with_body() {
    parse_ok("fn fib(n):\n    if n <= 1:\n        return n\n    return fib(n - 1) + fib(n - 2)");
}

// Generics use angle brackets: <T>
#[test]
fn parse_generic_function() {
    parse_ok("fn identity<T>(x: T) -> T:\n    return x");
}

// Where clause tests
#[test]
fn parse_function_where_clause() {
    parse_ok("fn show<T>(x: T) where T: Display:\n    return x");
}

#[test]
fn parse_function_where_clause_multiple_bounds() {
    parse_ok("fn process<T>(x: T) where T: Clone + Debug:\n    return x");
}

#[test]
fn parse_function_where_clause_multiple_params() {
    parse_ok("fn combine<T, U>(a: T, b: U) where T: Clone, U: Copy:\n    return a");
}

// Named arguments use = not :
#[test]
fn parse_named_arguments() {
    parse_ok("let x = foo(a = 1, b = 2)");
}

#[test]
fn parse_labeled_tuple_return_type() {
    let items = parse("fn div_rem(n: i64, d: i64) -> (quotient: i64, remainder: i64):\n    return (quotient: n / d, remainder: n % d)");
    let Node::Function(f) = &items[0] else {
        panic!("expected function");
    };
    let Some(Type::LabeledTuple(fields)) = &f.return_type else {
        panic!("expected labeled tuple return type");
    };
    assert_eq!(fields[0].label, "quotient");
    assert_eq!(fields[1].label, "remainder");
}

#[test]
fn parse_labeled_tuple_expression() {
    let items =
        parse("fn full_add(a: bool, b: bool) -> (sum: bool, carry: bool):\n    return (sum: a or b, carry: a and b)");
    let Node::Function(f) = &items[0] else {
        panic!("expected function");
    };
    let Node::Return(ret) = &f.body.statements[0] else {
        panic!("expected return");
    };
    let Some(Expr::LabeledTuple(fields)) = &ret.value else {
        panic!("expected labeled tuple expression");
    };
    assert_eq!(fields[0].label, "sum");
    assert_eq!(fields[1].label, "carry");
}

#[test]
fn rejects_mixed_labeled_tuple_return_type() {
    let mut parser = Parser::new("fn bad() -> (sum: bool, bool):\n    return (true, false)");
    let err = parser.parse().expect_err("mixed tuple labels should fail");
    assert!(format!("{err:?}").contains("expected"));
}

#[test]
fn rejects_duplicate_labeled_tuple_return_type() {
    let mut parser = Parser::new("fn bad() -> (sum: bool, sum: bool):\n    return (sum: true, sum: false)");
    let err = parser.parse().expect_err("duplicate tuple labels should fail");
    assert!(format!("{err:?}").contains("duplicate tuple field label"));
}

// Default parameters
#[test]
fn parse_default_parameters() {
    parse_ok("fn greet(name = 'World'):\n    return name");
}

// Lambda expressions
#[test]
fn parse_lambda_expression() {
    parse_ok(r"let f = \x: x + 1");
    parse_ok(r"let f = \a, b: a + b");
    parse_ok(r"let f = \: 42");
}

// Extern function
#[test]
fn parse_extern_function() {
    let items = parse("extern fn add(a: i64, b: i64) -> i64");
    if let Node::Extern(e) = &items[0] {
        assert_eq!(e.name, "add");
    } else {
        panic!("expected extern");
    }
}

// Macro - syntax is: macro name(params) -> (contract): body
#[test]
fn parse_macro_definition() {
    let items = parse("macro double(x: Int) -> (returns result: Int):\n    emit result:\n        x + x");
    if let Node::Macro(m) = &items[0] {
        assert_eq!(m.name, "double");
    } else {
        panic!("expected macro");
    }
}

// Actor definition
#[test]
fn parse_actor_definition() {
    parse_ok("actor Counter:\n    fn increment():\n        return 0");
}

// Send/recv
#[test]
fn parse_send_recv() {
    parse_ok("let x = recv()");
    parse_ok("send(h, msg)");
}
