use simple_parser::ast::*;
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

fn parse_err(src: &str) {
    let mut parser = Parser::new(src);
    assert!(parser.parse().is_err(), "should fail to parse");
}

// Statements
#[test]
fn parse_let_statement() {
    let items = parse("let x = 42");
    assert_eq!(items.len(), 1);
    assert!(matches!(&items[0], Node::Let(_)));
}

#[test]
fn parse_let_mut_statement() {
    let items = parse("let mut x = 42");
    assert!(matches!(&items[0], Node::Let(_)));
}

#[test]
fn parse_const_statement() {
    let items = parse("const X = 100");
    assert!(matches!(&items[0], Node::Const(_)));
}

#[test]
fn parse_static_statement() {
    let items = parse("static counter = 0");
    assert!(matches!(&items[0], Node::Static(_)));
}

#[test]
fn parse_static_mut_statement() {
    let items = parse("static mut counter = 0");
    assert!(matches!(&items[0], Node::Static(_)));
}

// Control flow
#[test]
fn parse_if_statement() {
    let items = parse("if x > 0:\n    y = 1");
    assert!(matches!(&items[0], Node::If(_)));
}

#[test]
fn parse_if_else_statement() {
    parse_ok("if x > 0:\n    y = 1\nelse:\n    y = 0");
}

#[test]
fn parse_while_loop() {
    let items = parse("while x < 10:\n    x = x + 1");
    assert!(matches!(&items[0], Node::While(_)));
}

#[test]
fn parse_for_loop() {
    let items = parse("for i in range(0, 10):\n    sum = sum + i");
    assert!(matches!(&items[0], Node::For(_)));
}

#[test]
fn parse_match_statement() {
    let items = parse("match x:\n    1 =>\n        y = 1\n    _ =>\n        y = 0");
    assert!(matches!(&items[0], Node::Match(_)));
}

// Functions
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

// Struct and class
#[test]
fn parse_struct_definition() {
    let items = parse("struct Point:\n    x: i64\n    y: i64");
    if let Node::Struct(s) = &items[0] {
        assert_eq!(s.name, "Point");
        assert_eq!(s.fields.len(), 2);
    } else {
        panic!("expected struct");
    }
}

#[test]
fn parse_class_definition() {
    let items = parse("class Counter:\n    fn count():\n        return 0");
    if let Node::Class(c) = &items[0] {
        assert_eq!(c.name, "Counter");
        assert_eq!(c.methods.len(), 1);
    } else {
        panic!("expected class");
    }
}

// Enum
#[test]
fn parse_enum_definition() {
    let items = parse("enum Color:\n    Red\n    Green\n    Blue");
    if let Node::Enum(e) = &items[0] {
        assert_eq!(e.name, "Color");
        assert_eq!(e.variants.len(), 3);
    } else {
        panic!("expected enum");
    }
}

#[test]
fn parse_enum_with_payload() {
    let items = parse("enum Option:\n    Some(i64)\n    None");
    if let Node::Enum(e) = &items[0] {
        assert_eq!(e.variants.len(), 2);
    } else {
        panic!("expected enum");
    }
}

// Impl blocks
#[test]
fn parse_impl_block() {
    let items = parse("impl Point:\n    fn origin():\n        return Point { x: 0, y: 0 }");
    if let Node::Impl(i) = &items[0] {
        assert_eq!(i.methods.len(), 1);
    } else {
        panic!("expected impl");
    }
}

// Trait
#[test]
fn parse_trait_definition() {
    let items = parse("trait Show:\n    fn show(self):\n        return 0");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.name, "Show");
    } else {
        panic!("expected trait");
    }
}

// Extern
#[test]
fn parse_extern_function() {
    let items = parse("extern fn add(a: i64, b: i64) -> i64");
    if let Node::Extern(e) = &items[0] {
        assert_eq!(e.name, "add");
    } else {
        panic!("expected extern");
    }
}

// Macro - syntax is: macro name!(params): body
#[test]
fn parse_macro_definition() {
    let items = parse("macro double!($x):\n    $x + $x");
    if let Node::Macro(m) = &items[0] {
        assert_eq!(m.name, "double");
    } else {
        panic!("expected macro");
    }
}

#[test]
fn parse_main_binding() {
    parse_ok("main = 42");
}

#[test]
fn parse_return_statement() {
    parse_ok("fn test():\n    return 42");
}

// break/continue need newline after them
#[test]
fn parse_break_continue() {
    parse_ok("while true:\n    break\n");
    parse_ok("while true:\n    continue\n");
}

#[test]
fn parse_assignment_statement() {
    let items = parse("x = 42");
    assert!(matches!(&items[0], Node::Assignment(_)));
}

#[test]
fn parse_augmented_assignment() {
    parse_ok("x += 1");
    parse_ok("x -= 1");
    parse_ok("x *= 2");
    parse_ok("x /= 2");
}

#[test]
fn parse_context_statement() {
    parse_ok("context obj:\n    x = 1");
}

// Additional edge cases for coverage
#[test]
fn parse_nested_expressions() {
    parse_ok("let x = ((1 + 2) * 3)");
    parse_ok("let arr = [[1, 2], [3, 4]]");
}

#[test]
fn parse_chained_method_calls() {
    parse_ok("let x = obj.method1().method2().method3()");
}

// Uses 'elif' not 'else if'
#[test]
fn parse_complex_if_else() {
    parse_ok("if a:\n    x = 1\nelif b:\n    x = 2\nelse:\n    x = 3");
}

// Generics use angle brackets: <T>
#[test]
fn parse_generic_function() {
    parse_ok("fn identity<T>(x: T) -> T:\n    return x");
}

#[test]
fn parse_generic_struct() {
    parse_ok("struct Box<T>:\n    value: T");
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

#[test]
fn parse_struct_where_clause() {
    let items = parse("struct Container<T> where T: Clone:\n    value: T");
    assert_eq!(items.len(), 1);
    if let Node::Struct(s) = &items[0] {
        assert_eq!(s.name, "Container");
        assert_eq!(s.where_clause.len(), 1);
        assert_eq!(s.where_clause[0].type_param, "T");
        assert_eq!(s.where_clause[0].bounds, vec!["Clone"]);
    } else {
        panic!("Expected struct");
    }
}

#[test]
fn parse_trait_where_clause() {
    parse_ok("trait Comparable<T> where T: Ord:\n    fn compare(self, other: T) -> i64:\n        return 0");
}

#[test]
fn parse_impl_where_clause() {
    parse_ok("impl<T> Clone for Container[T] where T: Clone:\n    fn clone(self) -> Container[T]:\n        return Container(self.value)");
}

#[test]
fn parse_impl_generic_params() {
    let items = parse("impl<T> Clone for Container[T] where T: Clone:\n    fn clone(self) -> Container[T]:\n        return self");
    if let Node::Impl(impl_block) = &items[0] {
        assert_eq!(impl_block.generic_params, vec!["T"]);
        assert_eq!(impl_block.trait_name, Some("Clone".to_string()));
        assert_eq!(impl_block.where_clause.len(), 1);
        assert_eq!(impl_block.where_clause[0].type_param, "T");
    } else {
        panic!("Expected impl block");
    }
}

#[test]
fn parse_trait_impl() {
    parse_ok("impl Show for Point:\n    fn show(self):\n        return 0");
}

// Default trait implementation tests
#[test]
fn parse_trait_abstract_method() {
    // Trait with abstract method (no body)
    let items = parse("trait Greet:\n    fn greet(self) -> str");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.methods.len(), 1);
        assert!(t.methods[0].is_abstract);
        assert_eq!(t.methods[0].name, "greet");
    } else {
        panic!("Expected trait");
    }
}

#[test]
fn parse_trait_default_method() {
    // Trait with default implementation
    let items = parse("trait Greet:\n    fn greet(self) -> str:\n        return 'Hello'");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.methods.len(), 1);
        assert!(!t.methods[0].is_abstract);
        assert_eq!(t.methods[0].name, "greet");
    } else {
        panic!("Expected trait");
    }
}

#[test]
fn parse_trait_mixed_methods() {
    // Trait with both abstract and default methods
    let items = parse("trait Animal:\n    fn speak(self) -> str\n    fn sleep(self):\n        return 0");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.methods.len(), 2);
        // speak is abstract (no body)
        assert!(t.methods[0].is_abstract);
        assert_eq!(t.methods[0].name, "speak");
        // sleep has default implementation
        assert!(!t.methods[1].is_abstract);
        assert_eq!(t.methods[1].name, "sleep");
    } else {
        panic!("Expected trait");
    }
}

// Associated types tests
#[test]
fn parse_trait_associated_type_simple() {
    // Trait with simple associated type
    let items = parse("trait Iterator:\n    type Item\n    fn next(self) -> Item");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.name, "Iterator");
        assert_eq!(t.associated_types.len(), 1);
        assert_eq!(t.associated_types[0].name, "Item");
        assert!(t.associated_types[0].bounds.is_empty());
        assert!(t.associated_types[0].default.is_none());
        assert_eq!(t.methods.len(), 1);
    } else {
        panic!("Expected trait");
    }
}

#[test]
fn parse_trait_associated_type_with_bounds() {
    // Associated type with trait bounds
    let items = parse("trait Collection:\n    type Item: Clone + Default\n    fn get(self) -> Item");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.associated_types.len(), 1);
        assert_eq!(t.associated_types[0].name, "Item");
        assert_eq!(t.associated_types[0].bounds, vec!["Clone", "Default"]);
    } else {
        panic!("Expected trait");
    }
}

#[test]
fn parse_trait_associated_type_with_default() {
    // Associated type with default type
    let items = parse("trait Container:\n    type Item = i64\n    fn get(self) -> Item");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.associated_types.len(), 1);
        assert_eq!(t.associated_types[0].name, "Item");
        assert!(t.associated_types[0].default.is_some());
    } else {
        panic!("Expected trait");
    }
}

#[test]
fn parse_impl_associated_type() {
    // Impl block with associated type implementation
    let items = parse("impl Iterator for List:\n    type Item = i64\n    fn next(self) -> i64:\n        return 0");
    if let Node::Impl(impl_block) = &items[0] {
        assert_eq!(impl_block.associated_types.len(), 1);
        assert_eq!(impl_block.associated_types[0].name, "Item");
        assert_eq!(impl_block.methods.len(), 1);
    } else {
        panic!("Expected impl block");
    }
}

#[test]
fn parse_trait_multiple_associated_types() {
    // Multiple associated types
    let items = parse("trait Map:\n    type Key\n    type Value\n    fn get(self, k: Key) -> Value");
    if let Node::Trait(t) = &items[0] {
        assert_eq!(t.associated_types.len(), 2);
        assert_eq!(t.associated_types[0].name, "Key");
        assert_eq!(t.associated_types[1].name, "Value");
    } else {
        panic!("Expected trait");
    }
}

// Generic types use brackets: List[i64]
#[test]
fn parse_type_alias() {
    parse_ok("type IntList = List[i64]");
}

// Named arguments use = not :
#[test]
fn parse_named_arguments() {
    parse_ok("let x = foo(a = 1, b = 2)");
}

#[test]
fn parse_default_parameters() {
    parse_ok("fn greet(name = 'World'):\n    return name");
}

#[test]
fn parse_tuple_pattern() {
    parse_ok("let (a, b) = (1, 2)");
}

#[test]
fn parse_match_with_guard() {
    parse_ok("match x:\n    n if n > 0 =>\n        y = 1\n    _ =>\n        y = 0");
}

#[test]
fn parse_actor_definition() {
    parse_ok("actor Counter:\n    fn increment():\n        return 0");
}

#[test]
fn parse_send_recv() {
    parse_ok("let x = recv()");
    parse_ok("send(h, msg)");
}

// Loop with break - needs newline after break
#[test]
fn parse_loop_statement() {
    parse_ok("loop:\n    x = x + 1\n    if x > 10:\n        break\n");
}

// Expressions
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

#[test]
fn parse_comparison_operations() {
    parse_ok("let x = 1 < 2");
    parse_ok("let x = 1 > 2");
    parse_ok("let x = 1 <= 2");
    parse_ok("let x = 1 >= 2");
    parse_ok("let x = 1 == 2");
    parse_ok("let x = 1 != 2");
}

#[test]
fn parse_logical_operations() {
    parse_ok("let x = true and false");
    parse_ok("let x = true or false");
    parse_ok("let x = not true");
}

#[test]
fn parse_unary_operations() {
    parse_ok("let x = -5");
    parse_ok("let x = not true");
    parse_ok("let x = ~42");
}

#[test]
fn parse_collections() {
    parse_ok("let arr = [1, 2, 3]");
    parse_ok("let arr = []");
    parse_ok("let t = (1, 2, 3)");
    parse_ok("let t = ()");
    parse_ok(r#"let d = {"a": 1, "b": 2}"#);
    parse_ok("let d = {}");
}

#[test]
fn parse_indexing() {
    parse_ok("let x = arr[0]");
    parse_ok("let x = arr[i]");
    parse_ok("let x = arr[1 + 2]");
}

#[test]
fn parse_function_call_expression() {
    parse_ok("let x = foo()");
    parse_ok("let x = foo(1)");
    parse_ok("let x = foo(1, 2, 3)");
}

#[test]
fn parse_method_call_expression() {
    parse_ok("let x = obj.method()");
    parse_ok("let x = obj.method(1)");
    parse_ok("let x = obj.method(1, 2)");
}

#[test]
fn parse_field_access_expression() {
    parse_ok("let x = obj.field");
    parse_ok("let x = obj.field1.field2");
}

#[test]
fn parse_lambda_expression() {
    parse_ok(r"let f = \x: x + 1");
    parse_ok(r"let f = \a, b: a + b");
    parse_ok(r"let f = \: 42");
}

#[test]
fn parse_if_expression() {
    parse_ok("let x = if true: 1 else: 0");
    parse_ok("let x = if a > b: a else: b");
}

#[test]
fn parse_struct_init_expression() {
    parse_ok("let p = Point { x: 1, y: 2 }");
    parse_ok("let p = Point {}");
}

#[test]
fn parse_path_expression() {
    parse_ok("let c = Color::Red");
    parse_ok("let x = Mod::Func()");
}

#[test]
fn parse_new_expression() {
    parse_ok("let p = new & 42");
    parse_ok("let p = new * 42");
}

#[test]
fn parse_spawn_expression() {
    parse_ok("let h = spawn work()");
}

#[test]
fn parse_is_in_expression() {
    parse_ok("let x = a is None");
    parse_ok("let x = a in list");
}

// Error cases
#[test]
fn parse_unclosed_paren() {
    parse_err("let x = (1 + 2");
}

#[test]
fn parse_unclosed_bracket() {
    parse_err("let x = [1, 2, 3");
}

#[test]
fn parse_missing_colon() {
    parse_err("if x > 0\n    y = 1");
}

#[test]
fn parse_missing_indent() {
    parse_err("if x > 0:");
}

// Complex programs
#[test]
fn parse_multiple_statements() {
    parse_ok("let x = 1\nlet y = 2\nlet z = x + y");
}

#[test]
fn parse_function_with_body() {
    parse_ok("fn fib(n):\n    if n <= 1:\n        return n\n    return fib(n - 1) + fib(n - 2)");
}

// 'new' is a keyword, use 'init' instead
#[test]
fn parse_class_with_methods() {
    parse_ok("class Point:\n    fn init(x, y):\n        self.x = x\n        self.y = y\n    fn distance():\n        return 0");
}

// Match patterns use full enum paths or simple identifiers
#[test]
fn parse_match_with_patterns() {
    parse_ok("match opt:\n    Option::Some(x) =>\n        x\n    Option::None =>\n        0");
}

/// `expect await f == 42` should parse as `expect((await f) == 42)`
/// This tests that `await` is recognized as starting an argument in no-paren calls.
#[test]
fn test_expect_await_parsing() {
    let items = parse("expect await f == 42");
    // Should parse as a single expression (function call), not two separate statements
    assert_eq!(items.len(), 1, "should be single statement, not two");
    // The expression should be a call to 'expect'
    match &items[0] {
        Node::Expression(Expr::Call { callee, args }) => {
            assert!(matches!(**callee, Expr::Identifier(ref name) if name == "expect"));
            assert_eq!(args.len(), 1);
            // The argument should be: (await f) == 42
            match &args[0].value {
                Expr::Binary { op: BinOp::Eq, left, right } => {
                    assert!(matches!(**left, Expr::Await(_)));
                    assert!(matches!(**right, Expr::Integer(42)));
                }
                other => panic!("expected Binary Eq, got {:#?}", other),
            }
        }
        other => panic!("expected Call expression, got {:#?}", other),
    }
}

// === dyn Trait Tests ===

#[test]
fn parse_dyn_trait_type_annotation() {
    // dyn Trait as type annotation in function parameter
    parse_ok("fn process(obj: dyn Display):\n    pass");
}

#[test]
fn parse_dyn_trait_return_type() {
    // dyn Trait as function return type
    parse_ok("fn create() -> dyn Printable:\n    pass");
}

#[test]
fn parse_dyn_trait_in_array() {
    // Array of dyn Trait objects
    parse_ok("let items: [dyn Drawable] = []");
}

#[test]
fn parse_dyn_trait_parses_correctly() {
    let items = parse("fn take(x: dyn Trait):\n    pass");
    if let Node::Function(f) = &items[0] {
        assert_eq!(f.params.len(), 1);
        assert!(matches!(&f.params[0].ty, Some(Type::DynTrait(name)) if name == "Trait"));
    } else {
        panic!("expected function");
    }
}

// === Unit Arithmetic Tests ===

#[test]
fn parse_unit_family_basic() {
    // Basic unit family without arithmetic
    let items = parse("unit length(base: f64): m = 1.0, km = 1000.0");
    if let Node::UnitFamily(uf) = &items[0] {
        assert_eq!(uf.name, "length");
        assert_eq!(uf.variants.len(), 2);
        assert_eq!(uf.variants[0].suffix, "m");
        assert_eq!(uf.variants[0].factor, 1.0);
        assert_eq!(uf.variants[1].suffix, "km");
        assert_eq!(uf.variants[1].factor, 1000.0);
        assert!(uf.arithmetic.is_none());
    } else {
        panic!("expected UnitFamily");
    }
}

#[test]
fn parse_unit_family_with_arithmetic() {
    // Unit family with arithmetic rules
    let code = r#"unit length(base: f64): m = 1.0, km = 1000.0:
    allow add(length) -> length
    allow sub(length) -> length
    allow mul(f64) -> length
    allow neg -> length"#;
    let items = parse(code);
    if let Node::UnitFamily(uf) = &items[0] {
        assert_eq!(uf.name, "length");
        let arith = uf.arithmetic.as_ref().expect("arithmetic");
        assert_eq!(arith.binary_rules.len(), 3);
        assert_eq!(arith.unary_rules.len(), 1);
        // Check binary rules
        assert!(matches!(arith.binary_rules[0].op, BinaryArithmeticOp::Add));
        assert!(matches!(arith.binary_rules[1].op, BinaryArithmeticOp::Sub));
        assert!(matches!(arith.binary_rules[2].op, BinaryArithmeticOp::Mul));
        // Check unary rules
        assert!(matches!(arith.unary_rules[0].op, UnaryArithmeticOp::Neg));
    } else {
        panic!("expected UnitFamily");
    }
}

#[test]
fn parse_unit_family_with_custom_fn() {
    // Unit family with custom function
    let code = r#"unit length(base: f64): m = 1.0:
    allow add(length) -> length
    fn sqrt(self) -> f64:
        return sqrt(self.value())"#;
    let items = parse(code);
    if let Node::UnitFamily(uf) = &items[0] {
        let arith = uf.arithmetic.as_ref().expect("arithmetic");
        assert_eq!(arith.binary_rules.len(), 1);
        assert_eq!(arith.custom_fns.len(), 1);
        assert_eq!(arith.custom_fns[0].name, "sqrt");
    } else {
        panic!("expected UnitFamily");
    }
}

#[test]
fn parse_compound_unit_basic() {
    // Simple compound unit
    let items = parse("unit velocity = length / time");
    if let Node::CompoundUnit(cu) = &items[0] {
        assert_eq!(cu.name, "velocity");
        assert!(matches!(&cu.expr, UnitExpr::Div(_, _)));
        assert!(cu.arithmetic.is_none());
    } else {
        panic!("expected CompoundUnit");
    }
}

#[test]
fn parse_compound_unit_with_power() {
    // Compound unit with exponent
    let items = parse("unit acceleration = length / time^2");
    if let Node::CompoundUnit(cu) = &items[0] {
        assert_eq!(cu.name, "acceleration");
        if let UnitExpr::Div(left, right) = &cu.expr {
            assert!(matches!(left.as_ref(), UnitExpr::Base(n) if n == "length"));
            assert!(matches!(right.as_ref(), UnitExpr::Pow(_, 2)));
        } else {
            panic!("expected Div");
        }
    } else {
        panic!("expected CompoundUnit");
    }
}

#[test]
fn parse_compound_unit_with_arithmetic() {
    // Compound unit with arithmetic rules
    let code = r#"unit velocity = length / time:
    allow add(velocity) -> velocity
    allow mul(time) -> length"#;
    let items = parse(code);
    if let Node::CompoundUnit(cu) = &items[0] {
        assert_eq!(cu.name, "velocity");
        let arith = cu.arithmetic.as_ref().expect("arithmetic");
        assert_eq!(arith.binary_rules.len(), 2);
        // velocity + velocity -> velocity
        assert!(matches!(arith.binary_rules[0].op, BinaryArithmeticOp::Add));
        // velocity * time -> length
        assert!(matches!(arith.binary_rules[1].op, BinaryArithmeticOp::Mul));
    } else {
        panic!("expected CompoundUnit");
    }
}

#[test]
fn parse_compound_unit_multiplication() {
    // Compound unit with multiplication
    let items = parse("unit area = length * length");
    if let Node::CompoundUnit(cu) = &items[0] {
        assert_eq!(cu.name, "area");
        assert!(matches!(&cu.expr, UnitExpr::Mul(_, _)));
    } else {
        panic!("expected CompoundUnit");
    }
}

#[test]
fn parse_compound_unit_complex() {
    // Complex compound unit: force = mass * length / time^2
    let items = parse("unit force = mass * length / time^2");
    if let Node::CompoundUnit(cu) = &items[0] {
        assert_eq!(cu.name, "force");
        // Should parse as (mass * length) / time^2
        if let UnitExpr::Div(left, right) = &cu.expr {
            assert!(matches!(left.as_ref(), UnitExpr::Mul(_, _)));
            assert!(matches!(right.as_ref(), UnitExpr::Pow(_, 2)));
        } else {
            panic!("expected Div");
        }
    } else {
        panic!("expected CompoundUnit");
    }
}
