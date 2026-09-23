use simple_parser::{ast::Node, FunctionDef, Parser};

fn methods(source: &str) -> Vec<FunctionDef> {
    let module = Parser::new(source).parse().expect("receiver fixture parses");
    match module.items.into_iter().next().unwrap() {
        Node::Class(value) => value.methods,
        Node::Struct(value) => value.methods,
        _ => panic!("expected class or struct"),
    }
}

#[test]
fn implicit_receiver_metadata_matches_class_and_value_methods() {
    for owner in ["class", "struct"] {
        let source = format!("{owner} Counter:\n    value: i64\n    fn read(delta: i64) -> i64:\n        self.value + delta\n");
        let functions = methods(&source);
        let method = &functions[0];
        assert!(!method.is_static);
        assert_eq!(method.params.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(), ["self", "delta"]);
    }
}

#[test]
fn explicit_receiver_is_not_duplicated_and_true_static_is_unchanged() {
    let functions = methods("class Counter:\n    value: i64\n    fn read(self, delta: i64) -> i64:\n        self.value + delta\n    static fn fixed(delta: i64) -> i64:\n        delta + 2\n    fn wrap(delta: i64) -> Counter:\n        Counter(value: delta)\n    static fn new(delta: i64) -> Counter:\n        Counter(value: delta)\n");
    assert!(!functions[0].is_static);
    assert_eq!(functions[0].params.len(), 2);
    for function in &functions[1..] {
        assert!(function.is_static, "{}", function.name);
        assert_eq!(function.params.len(), 1, "{}", function.name);
    }
}

#[test]
fn nested_receiver_use_and_stack_arguments_are_exported() {
    let functions = methods("class Counter:\n    value: i64\n    fn stack(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64, i: i64) -> i64:\n        if a > 0:\n            return self.value + a + b + c + d + e + f + g + h + i\n        0\n");
    assert!(!functions[0].is_static);
    assert_eq!(functions[0].params.len(), 10);
    assert_eq!(functions[0].params[0].name, "self");
}

#[test]
fn mutable_receiver_injection_remains_single() {
    let functions = methods("class Counter:\n    value: i64\n    me set(value: i64):\n        self.value = value\n");
    assert!(!functions[0].is_static);
    assert!(functions[0].is_me_method);
    assert_eq!(functions[0].params.len(), 2);
    assert_eq!(functions[0].params[0].name, "self");
}
