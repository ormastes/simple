//! Bug: doc/08_tracking/bug/on_is_an_undocumented_reserved_word_2026-08-02.md
//!
//! `on` stays reserved (AOP advice `on pc{...} use X`). When it is used as a
//! statement-leading name that is not an assignment/field access, the error
//! must name the keyword instead of complaining about a `pc{...}` the user
//! never wrote.

use simple_parser::Parser;

fn parse_err(src: &str) -> String {
    let mut parser = Parser::new(src);
    match parser.parse() {
        Ok(_) => panic!("expected parse error for:\n{src}"),
        Err(e) => format!("{e}"),
    }
}

#[test]
fn on_in_statement_position_names_reserved_keyword() {
    for src in ["val on = 1\non + 1\n", "var on = 5\non + 1\n"] {
        let msg = parse_err(src);
        assert!(
            msg.contains("`on` is a reserved keyword and cannot be used as an identifier"),
            "message must name `on` as reserved, got: {msg}"
        );
    }
}

#[test]
fn on_assign_and_field_still_parse() {
    let mut p = Parser::new("var on = 5\non = on + 1\n");
    assert!(p.parse().is_ok());
}

#[test]
fn real_advice_still_parses() {
    let mut p = Parser::new("on pc{ execution(* User.new(..)) } use LoggingInterceptor\n");
    assert!(p.parse().is_ok());
}
