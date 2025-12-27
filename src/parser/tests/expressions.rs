use simple_parser::Parser;

fn parse_ok(src: &str) {
    let mut parser = Parser::new(src);
    parser.parse().expect("should parse");
}

// Nested expressions
#[test]
fn parse_nested_expressions() {
    parse_ok("let x = ((1 + 2) * 3)");
    parse_ok("let arr = [[1, 2], [3, 4]]");
}

// Chained method calls
#[test]
fn parse_chained_method_calls() {
    parse_ok("let x = obj.method1().method2().method3()");
}

// Literals
#[test]
fn parse_literals() {
    parse_ok("let x = 42");
    parse_ok("let x = 3.14");
    parse_ok("let x = true");
    parse_ok("let x = false");
    parse_ok("let x = nil");
    parse_ok("let x = 'hello'");
    parse_ok(r#"let x = "hello""#);
    parse_ok("let x = :symbol");
}

// Binary operations
#[test]
fn parse_binary_operations() {
    parse_ok("let x = 1 + 2");
    parse_ok("let x = 1 - 2");
    parse_ok("let x = 1 * 2");
    parse_ok("let x = 1 / 2");
    parse_ok("let x = 1 % 2");
    parse_ok("let x = 2 ** 3");
    parse_ok("let x = 7 // 3");
}

// Comparison operations
#[test]
fn parse_comparison_operations() {
    parse_ok("let x = 1 < 2");
    parse_ok("let x = 1 > 2");
    parse_ok("let x = 1 <= 2");
    parse_ok("let x = 1 >= 2");
    parse_ok("let x = 1 == 2");
    parse_ok("let x = 1 != 2");
}

// Logical operations
#[test]
fn parse_logical_operations() {
    parse_ok("let x = true and false");
    parse_ok("let x = true or false");
    parse_ok("let x = not true");
}

// Unary operations
#[test]
fn parse_unary_operations() {
    parse_ok("let x = -5");
    parse_ok("let x = not true");
    parse_ok("let x = ~42");
}

// Collections
#[test]
fn parse_collections() {
    parse_ok("let arr = [1, 2, 3]");
    parse_ok("let arr = []");
    parse_ok("let t = (1, 2, 3)");
    parse_ok("let t = ()");
    parse_ok(r#"let d = {"a": 1, "b": 2}"#);
    parse_ok("let d = {}");
}

// Tuple pattern
#[test]
fn parse_tuple_pattern() {
    parse_ok("let (a, b) = (1, 2)");
}

// Indexing
#[test]
fn parse_indexing() {
    parse_ok("let x = arr[0]");
    parse_ok("let x = arr[i]");
    parse_ok("let x = arr[1 + 2]");
}

// Function call expression
#[test]
fn parse_function_call_expression() {
    parse_ok("let x = foo()");
    parse_ok("let x = foo(1)");
    parse_ok("let x = foo(1, 2, 3)");
}

// Method call expression
#[test]
fn parse_method_call_expression() {
    parse_ok("let x = obj.method()");
    parse_ok("let x = obj.method(1)");
    parse_ok("let x = obj.method(1, 2)");
}

// Field access expression
#[test]
fn parse_field_access_expression() {
    parse_ok("let x = obj.field");
    parse_ok("let x = obj.field1.field2");
}

// If expression
#[test]
fn parse_if_expression() {
    parse_ok("let x = if true: 1 else: 0");
    parse_ok("let x = if a > b: a else: b");
}

// Path expression
#[test]
fn parse_path_expression() {
    parse_ok("let c = Color::Red");
    parse_ok("let x = Mod::Func()");
}

// New expression
#[test]
fn parse_new_expression() {
    parse_ok("let p = new & 42");
    parse_ok("let p = new * 42");
}

// Spawn expression
#[test]
fn parse_spawn_expression() {
    parse_ok("let h = spawn work()");
}

// Is/in expression
#[test]
fn parse_is_in_expression() {
    parse_ok("let x = a is None");
    parse_ok("let x = a in list");
}
