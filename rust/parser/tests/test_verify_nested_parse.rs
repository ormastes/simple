use simple_parser::Parser;

#[test]
fn test_list_option_string_actually_parses() {
    // This is the same source as test_new_nested_generics_no_warning
    let src = "val x: List<Option<String>> = []";
    let mut parser = Parser::new(src);
    let result = parser.parse();

    match &result {
        Ok(module) => {
            println!("✓ Parse succeeded! Module has {} items", module.items.len());
        }
        Err(e) => {
            println!("✗ Parse FAILED: {:?}", e);
            panic!("The supposedly working nested generic test actually fails to parse!");
        }
    }

    // If we get here, parsing succeeded
    assert!(result.is_ok(), "Nested generics should parse successfully");
}
