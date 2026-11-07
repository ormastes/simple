use simple_parser::{ast::{AssignOp, Expr, Node}, Parser};

#[test]
fn vec_single_index_is_an_assignment_target() {
    for (operator, expected) in [("=", AssignOp::Assign), ("+=", AssignOp::AddAssign), ("-=", AssignOp::SubAssign)] {
        let source = format!("vec[i + 1] {operator} 7\n");
        let module = Parser::new(&source).parse().unwrap();
        let Node::Assignment(statement) = &module.items[0] else { panic!("not assignment") };
        assert_eq!(statement.op, expected);
        let Expr::Index { receiver, index } = &statement.target else { panic!("literal lvalue: {:?}", statement.target) };
        assert!(matches!(receiver.as_ref(), Expr::Identifier(name) if name == "vec"));
        assert!(matches!(index.as_ref(), Expr::Binary { .. }));
    }
}

#[test]
fn vec_rhs_and_multielement_target_keep_literal_syntax() {
    let module = Parser::new("value = vec[1]\nvec[1, 2] = 3\n").parse().unwrap();
    let Node::Assignment(rhs) = &module.items[0] else { panic!("not assignment") };
    assert!(matches!(&rhs.value, Expr::VecLiteral(values) if values.len() == 1));
    let Node::Assignment(target) = &module.items[1] else { panic!("not assignment") };
    assert!(matches!(&target.target, Expr::VecLiteral(values) if values.len() == 2));
}

#[test]
fn ordinary_index_and_vec_macro_remain_distinct() {
    let module = Parser::new("rows[2] = 7\nvalue = vec![1, 2]\n").parse().unwrap();
    let Node::Assignment(ordinary) = &module.items[0] else { panic!("not assignment") };
    assert!(matches!(&ordinary.target, Expr::Index { receiver, .. } if matches!(receiver.as_ref(), Expr::Identifier(name) if name == "rows")));
    let Node::Assignment(rhs) = &module.items[1] else { panic!("not assignment") };
    assert!(matches!(&rhs.value, Expr::MacroInvocation { name, .. } if name == "vec"));
}
