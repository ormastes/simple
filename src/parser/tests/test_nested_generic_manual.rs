use simple_parser::Parser;
use simple_parser::ast::Type;

#[test]
fn test_parse_nested_generic_type_only() {
    let src = "val x: Option<Guard<i32>>"; // Incomplete, just to test type parsing
    let mut parser = Parser::new(src);

    // Try to manually trigger type parsing
    // This won't work directly, but let's see the full error
    let result = parser.parse();

    match result {
        Ok(_module) => {
            println!("Parse succeeded!");
        }
        Err(e) => {
            println!("Parse error: {:?}", e);
            println!("Error message: {}", e);
            panic!("Parse failed - investigating nested generics");
        }
    }
}

#[test]
fn test_nested_generic_function_return() {
    let src = "fn test() -> Option<Guard<i32>>:\n    return nil";
    let mut parser = Parser::new(src);
    let result = parser.parse();

    match result {
        Ok(_module) => {
            println!("Parse succeeded!");
        }
        Err(e) => {
            panic!("Parse failed: {:?}", e);
        }
    }
}

#[test]
fn test_nested_generic_variable() {
    let src = "val x: Option<Guard<i32>> = nil";
    let mut parser = Parser::new(src);
    let result = parser.parse();

    match result {
        Ok(_module) => {
            println!("Parse succeeded!");
        }
        Err(e) => {
            panic!("Parse failed: {:?}", e);
        }
    }
}
