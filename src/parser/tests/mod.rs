use simple_parser::ast::*;
use simple_parser::Parser;

// Test helper functions
pub(crate) fn parse(src: &str) -> Vec<Node> {
    let mut parser = Parser::new(src);
    let module = parser.parse().expect("parse ok");
    module.items
}

pub(crate) fn parse_ok(src: &str) {
    let mut parser = Parser::new(src);
    parser.parse().expect("should parse");
}

pub(crate) fn parse_err(src: &str) {
    let mut parser = Parser::new(src);
    assert!(parser.parse().is_err(), "should fail to parse");
}

// Test modules
mod statements;
mod control_flow;
mod functions;
mod data_structures;
mod traits;
mod types;
mod expressions;
mod edge_cases;
mod enum_advanced;
