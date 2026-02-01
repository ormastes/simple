use simple_parser::ast::*;
use simple_parser::Parser;

fn parse(src: &str) -> Vec<Node> {
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("parse ok");
    module.items
}

// === Parameter call_site_label Tests ===

#[test]
fn param_with_to_label() {
    let items = parse("fn copy_from(from: text to, to: text):\n    pass");
    if let Node::Function(f) = &items[0] {
        assert_eq!(f.params.len(), 2);
        assert_eq!(f.params[0].name, "from");
        assert_eq!(f.params[0].call_site_label, Some("to".to_string()));
        assert_eq!(f.params[1].name, "to");
        assert_eq!(f.params[1].call_site_label, None);
    } else {
        panic!("expected function");
    }
}

#[test]
fn param_with_from_label() {
    let items = parse("fn transfer(amount: i64, src: Account from, dst: Account to):\n    pass");
    if let Node::Function(f) = &items[0] {
        assert_eq!(f.params.len(), 3);
        assert_eq!(f.params[0].call_site_label, None);
        assert_eq!(f.params[1].name, "src");
        assert_eq!(f.params[1].call_site_label, Some("from".to_string()));
        assert_eq!(f.params[2].name, "dst");
        assert_eq!(f.params[2].call_site_label, Some("to".to_string()));
    } else {
        panic!("expected function");
    }
}

#[test]
fn param_no_label() {
    let items = parse("fn add(a: i64, b: i64):\n    pass");
    if let Node::Function(f) = &items[0] {
        assert_eq!(f.params[0].call_site_label, None);
        assert_eq!(f.params[1].call_site_label, None);
    } else {
        panic!("expected function");
    }
}

#[test]
fn param_label_without_type() {
    let items = parse("fn move_item(item to):\n    pass");
    if let Node::Function(f) = &items[0] {
        assert_eq!(f.params[0].name, "item");
        assert_eq!(f.params[0].call_site_label, Some("to".to_string()));
    } else {
        panic!("expected function");
    }
}

// === All label keywords on parameters ===

#[test]
fn param_with_by_label() {
    let items = parse("fn scale(value: f64, factor: f64 by):\n    pass");
    if let Node::Function(f) = &items[0] {
        assert_eq!(f.params[1].name, "factor");
        assert_eq!(f.params[1].call_site_label, Some("by".to_string()));
    } else {
        panic!("expected function");
    }
}

#[test]
fn param_with_into_label() {
    let items = parse("fn convert(data: bytes, fmt: Format into):\n    pass");
    if let Node::Function(f) = &items[0] {
        assert_eq!(f.params[1].call_site_label, Some("into".to_string()));
    } else {
        panic!("expected function");
    }
}

#[test]
fn param_with_onto_label() {
    let items = parse("fn place(item: Widget, surface: Canvas onto):\n    pass");
    if let Node::Function(f) = &items[0] {
        assert_eq!(f.params[1].call_site_label, Some("onto".to_string()));
    } else {
        panic!("expected function");
    }
}

#[test]
fn param_with_with_label() {
    let items = parse("fn open(path: text, mode: Mode with):\n    pass");
    if let Node::Function(f) = &items[0] {
        assert_eq!(f.params[1].call_site_label, Some("with".to_string()));
    } else {
        panic!("expected function");
    }
}

// === All label keywords on arguments ===

#[test]
fn arg_with_to_label() {
    let items = parse("copy_from(src to, dst)");
    if let Node::Expression(Expr::Call { args, .. }) = &items[0] {
        assert_eq!(args.len(), 2);
        assert_eq!(args[0].label, Some("to".to_string()));
        assert_eq!(args[1].label, None);
    } else {
        panic!("expected call expression, got {:?}", items[0]);
    }
}

#[test]
fn arg_with_from_label() {
    let items = parse("transfer(100, checking from, savings to)");
    if let Node::Expression(Expr::Call { args, .. }) = &items[0] {
        assert_eq!(args.len(), 3);
        assert_eq!(args[0].label, None);
        assert_eq!(args[1].label, Some("from".to_string()));
        assert_eq!(args[2].label, Some("to".to_string()));
    } else {
        panic!("expected call expression, got {:?}", items[0]);
    }
}

#[test]
fn arg_with_by_label() {
    let items = parse("scale(10.0, 2.5 by)");
    if let Node::Expression(Expr::Call { args, .. }) = &items[0] {
        assert_eq!(args[1].label, Some("by".to_string()));
    } else {
        panic!("expected call expression");
    }
}

#[test]
fn arg_with_into_label() {
    let items = parse("convert(data, json into)");
    if let Node::Expression(Expr::Call { args, .. }) = &items[0] {
        assert_eq!(args[1].label, Some("into".to_string()));
    } else {
        panic!("expected call expression");
    }
}

#[test]
fn arg_with_onto_label() {
    let items = parse("place(widget, canvas onto)");
    if let Node::Expression(Expr::Call { args, .. }) = &items[0] {
        assert_eq!(args[1].label, Some("onto".to_string()));
    } else {
        panic!("expected call expression");
    }
}

#[test]
fn arg_with_with_label() {
    let items = parse("open(path, mode with)");
    if let Node::Expression(Expr::Call { args, .. }) = &items[0] {
        assert_eq!(args[1].label, Some("with".to_string()));
    } else {
        panic!("expected call expression");
    }
}

#[test]
fn arg_no_label() {
    let items = parse("add(1, 2)");
    if let Node::Expression(Expr::Call { args, .. }) = &items[0] {
        assert_eq!(args[0].label, None);
        assert_eq!(args[1].label, None);
    } else {
        panic!("expected call expression");
    }
}

#[test]
fn arg_label_with_named_arg_mix() {
    let items = parse("copy_from(src_path to, to: dest_path)");
    if let Node::Expression(Expr::Call { args, .. }) = &items[0] {
        assert_eq!(args.len(), 2);
        assert_eq!(args[0].name, None);
        assert_eq!(args[0].label, Some("to".to_string()));
        assert_eq!(args[1].name, Some("to".to_string()));
        assert_eq!(args[1].label, None);
    } else {
        panic!("expected call expression, got {:?}", items[0]);
    }
}

#[test]
fn arg_string_literal_with_label() {
    let items = parse("copy_from(\"/tmp/a.txt\" to, \"/tmp/b.txt\")");
    if let Node::Expression(Expr::Call { args, .. }) = &items[0] {
        assert_eq!(args[0].label, Some("to".to_string()));
        assert_eq!(args[1].label, None);
    } else {
        panic!("expected call expression");
    }
}

// === Round-trip: declaration + call site ===

#[test]
fn declaration_and_call_site_labels_match() {
    let decl_items = parse("fn convert(data: bytes, src: Format from, dst: Format to):\n    pass");
    let decl = if let Node::Function(f) = &decl_items[0] { f } else { panic!("expected function") };

    let call_items = parse("convert(raw_data, Format.JSON from, Format.XML to)");
    let call_args = if let Node::Expression(Expr::Call { args, .. }) = &call_items[0] { args } else { panic!("expected call") };

    assert_eq!(decl.params[1].call_site_label, call_args[1].label);
    assert_eq!(decl.params[2].call_site_label, call_args[2].label);
    assert_eq!(decl.params[1].call_site_label, Some("from".to_string()));
    assert_eq!(decl.params[2].call_site_label, Some("to".to_string()));
}

#[test]
fn declaration_and_call_by_label_match() {
    let decl_items = parse("fn scale(value: f64, factor: f64 by):\n    pass");
    let decl = if let Node::Function(f) = &decl_items[0] { f } else { panic!("expected function") };

    let call_items = parse("scale(10.0, 2.5 by)");
    let call_args = if let Node::Expression(Expr::Call { args, .. }) = &call_items[0] { args } else { panic!("expected call") };

    assert_eq!(decl.params[1].call_site_label, call_args[1].label);
    assert_eq!(decl.params[1].call_site_label, Some("by".to_string()));
}

// === Edge cases ===

#[test]
fn arg_label_on_integer_literal() {
    let items = parse("scale(10 from, 20 to)");
    if let Node::Expression(Expr::Call { args, .. }) = &items[0] {
        assert_eq!(args[0].label, Some("from".to_string()));
        assert_eq!(args[1].label, Some("to".to_string()));
    } else {
        panic!("expected call expression");
    }
}

#[test]
fn param_multiple_labels_different_types() {
    let items = parse("fn convert(data: bytes, src: Format from, dst: Format to):\n    pass");
    if let Node::Function(f) = &items[0] {
        assert_eq!(f.params[0].call_site_label, None);
        assert_eq!(f.params[1].call_site_label, Some("from".to_string()));
        assert_eq!(f.params[2].call_site_label, Some("to".to_string()));
    } else {
        panic!("expected function");
    }
}

#[test]
fn all_six_labels_in_one_function() {
    let items = parse("fn complex(a to, b from, c by, d into, e onto, f with):\n    pass");
    if let Node::Function(f) = &items[0] {
        assert_eq!(f.params[0].call_site_label, Some("to".to_string()));
        assert_eq!(f.params[1].call_site_label, Some("from".to_string()));
        assert_eq!(f.params[2].call_site_label, Some("by".to_string()));
        assert_eq!(f.params[3].call_site_label, Some("into".to_string()));
        assert_eq!(f.params[4].call_site_label, Some("onto".to_string()));
        assert_eq!(f.params[5].call_site_label, Some("with".to_string()));
    } else {
        panic!("expected function");
    }
}

#[test]
fn all_six_labels_in_call() {
    let items = parse("complex(a to, b from, c by, d into, e onto, f with)");
    if let Node::Expression(Expr::Call { args, .. }) = &items[0] {
        assert_eq!(args[0].label, Some("to".to_string()));
        assert_eq!(args[1].label, Some("from".to_string()));
        assert_eq!(args[2].label, Some("by".to_string()));
        assert_eq!(args[3].label, Some("into".to_string()));
        assert_eq!(args[4].label, Some("onto".to_string()));
        assert_eq!(args[5].label, Some("with".to_string()));
    } else {
        panic!("expected call expression");
    }
}

// === Keywords as identifiers still work ===

#[test]
fn by_as_named_argument() {
    let items = parse("func(by: 10)");
    if let Node::Expression(Expr::Call { args, .. }) = &items[0] {
        assert_eq!(args[0].name, Some("by".to_string()));
        assert_eq!(args[0].label, None);
    } else {
        panic!("expected call expression");
    }
}

#[test]
fn into_as_named_argument() {
    let items = parse("func(into: json)");
    if let Node::Expression(Expr::Call { args, .. }) = &items[0] {
        assert_eq!(args[0].name, Some("into".to_string()));
        assert_eq!(args[0].label, None);
    } else {
        panic!("expected call expression");
    }
}
