//! Regression tests for digit-led module path segments (e.g., `03_system`,
//! `01_unit`, `02_integration`, `03_sys`, `00.common`, `2d_math`).
//! Bug: doc/08_tracking/bug/db/use_digit_led_module_segment_lexed_as_typed_int_2026-11-27.sdn

use simple_parser::ast::{Expr, ImportTarget, Node};
use simple_parser::token::NumericSuffix;
use simple_parser::Parser;

fn parse_use(src: &str) -> simple_parser::ast::UseStmt {
    let mut parser = Parser::new(src);
    let module = parser
        .parse()
        .unwrap_or_else(|e| panic!("failed to parse `{src}`: {e:?}"));
    assert_eq!(module.items.len(), 1, "expected 1 item for `{src}`");
    match module.items.into_iter().next().unwrap() {
        Node::UseStmt(u) => u,
        other => panic!("expected UseStmt for `{src}`, got {other:?}"),
    }
}

#[test]
fn use_leading_digit_led_segment_group_import() {
    // Exact minimal repro from bug record
    let u = parse_use("use 03_sys.helper.{hello}");
    assert_eq!(u.path.segments, vec!["03_sys", "helper"]);
    assert_eq!(u.target, ImportTarget::Group(vec![ImportTarget::Single("hello".into())]));
}

#[test]
fn use_middle_digit_led_numbered_test_trees() {
    let u1 = parse_use("use test.03_system.os.os_ssh_spec");
    assert_eq!(u1.path.segments, vec!["test", "03_system", "os"]);
    assert_eq!(u1.target, ImportTarget::Single("os_ssh_spec".into()));

    let u2 = parse_use("use test.01_unit.compiler.foo.{bar, baz}");
    assert_eq!(u2.path.segments, vec!["test", "01_unit", "compiler", "foo"]);
    assert_eq!(
        u2.target,
        ImportTarget::Group(vec![
            ImportTarget::Single("bar".into()),
            ImportTarget::Single("baz".into()),
        ])
    );

    let u3 = parse_use("use test.02_integration.app.x.*");
    assert_eq!(u3.path.segments, vec!["test", "02_integration", "app", "x"]);
    assert_eq!(u3.target, ImportTarget::Glob);
}

#[test]
fn use_relative_digit_led_segments_and_alias() {
    let u1 = parse_use("use .03_sys.helper.{hello}");
    assert_eq!(u1.path.segments, vec![".", "03_sys", "helper"]);
    assert_eq!(u1.target, ImportTarget::Group(vec![ImportTarget::Single("hello".into())]));

    let u2 = parse_use("use ..03_sys.helper.hello as hi");
    assert_eq!(u2.path.segments, vec!["..", "03_sys", "helper"]);
    assert_eq!(
        u2.target,
        ImportTarget::Aliased {
            name: "hello".into(),
            alias: "hi".into(),
        }
    );

    // Space before `as` must not glue `as` onto `03_sys`.
    let u3 = parse_use("use 03_sys.helper as h");
    assert_eq!(u3.path.segments, vec!["03_sys"]);
    assert_eq!(
        u3.target,
        ImportTarget::Aliased {
            name: "helper".into(),
            alias: "h".into(),
        }
    );
}

#[test]
fn use_preserves_leading_zeros_and_consecutive_numeric_segments() {
    let u1 = parse_use("use 00.common.diagnostics.span");
    assert_eq!(u1.path.segments, vec!["00", "common", "diagnostics"]);
    assert_eq!(u1.target, ImportTarget::Single("span".into()));

    let u2 = parse_use("use 03.04_system.helper.{hello}");
    assert_eq!(u2.path.segments, vec!["03", "04_system", "helper"]);
    assert_eq!(u2.target, ImportTarget::Group(vec![ImportTarget::Single("hello".into())]));
}

#[test]
fn use_adjacent_alnum_type_suffix_and_radix_like_segments() {
    let u1 = parse_use("use 2d_math.vec2.{Vec2}");
    assert_eq!(u1.path.segments, vec!["2d_math", "vec2"]);
    assert_eq!(u1.target, ImportTarget::Group(vec![ImportTarget::Single("Vec2".into())]));

    let u2 = parse_use("use 03i64.mod_a.{f}");
    assert_eq!(u2.path.segments, vec!["03i64", "mod_a"]);
    assert_eq!(u2.target, ImportTarget::Group(vec![ImportTarget::Single("f".into())]));

    let u3 = parse_use("use 0b_bin.0o_oct.1e_exp.0x_hex.{x}");
    assert_eq!(u3.path.segments, vec!["0b_bin", "0o_oct", "1e_exp", "0x_hex"]);
    assert_eq!(u3.target, ImportTarget::Group(vec![ImportTarget::Single("x".into())]));
}

#[test]
fn export_and_from_import_accept_digit_led_segments() {
    let mut p1 = Parser::new("export 03_sys.helper.*");
    let m1 = p1.parse().expect("export 03_sys.helper.* should parse");
    match &m1.items[0] {
        Node::ExportUseStmt(e) => {
            assert_eq!(e.path.segments, vec!["03_sys", "helper"]);
            assert_eq!(e.target, ImportTarget::Glob);
        }
        other => panic!("expected ExportUseStmt, got {other:?}"),
    }

    let mut p2 = Parser::new("from test.03_system.os import helper");
    let m2 = p2.parse().expect("from test.03_system.os import helper should parse");
    match &m2.items[0] {
        Node::UseStmt(u) => {
            assert_eq!(u.path.segments, vec!["test", "03_system", "os"]);
            assert_eq!(u.target, ImportTarget::Single("helper".into()));
        }
        other => panic!("expected UseStmt, got {other:?}"),
    }
}

#[test]
fn typed_integer_unit_expression_unchanged() {
    let mut parser = Parser::new("val dist = 03_km");
    let module = parser.parse().expect("typed integer expression should still parse");
    match &module.items[0] {
        Node::Let(let_stmt) => match let_stmt.value.as_ref() {
            Some(Expr::TypedInteger(3, NumericSuffix::Unit(u))) if u == "km" => {}
            other => panic!("expected TypedInteger(3, Unit(\"km\")), got {other:?}"),
        },
        other => panic!("expected Let statement, got {other:?}"),
    }
}

#[test]
fn invalid_signed_exponent_in_use_path_still_rejected() {
    assert!(
        Parser::new("use 1.0e+5.foo").parse().is_err(),
        "1.0e+5 contains '+' and must not parse as a module path"
    );
}
