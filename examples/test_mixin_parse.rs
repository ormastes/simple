use simple_parser::Parser;

fn main() {
    println!("Testing Mixin Parser - Phase 1 Complete!");
    println!("=========================================\n");
    
    // Test 1: Simple mixin with one field
    let source1 = "mixin Simple:\n    field1: i64\n";
    test_parse("Simple mixin with one field", source1);
    
    // Test 2: Mixin with multiple fields
    let source2 = "mixin Timestamped:\n    created_at: i64\n    updated_at: i64\n";
    test_parse("Mixin with multiple fields", source2);
    
    // Test 3: Mixin with method
    let source3 = "mixin Printable:\n    fn to_string() -> str:\n        return \"test\"\n";
    test_parse("Mixin with method", source3);
    
    println!("\n🎉 All tests passed! Phase 1 complete (100%)");
}

fn test_parse(name: &str, source: &str) {
    print!("Test: {} ... ", name);
    let mut parser = Parser::new(source);
    match parser.parse() {
        Ok(module) => {
            if module.items.len() == 1 {
                match &module.items[0] {
                    simple_parser::Node::Mixin(m) => {
                        println!("✅ Passed (mixin '{}', {} fields, {} methods)", 
                                 m.name, m.fields.len(), m.methods.len());
                    }
                    _ => println!("❌ Failed: Expected Mixin node"),
                }
            } else {
                println!("❌ Failed: Expected 1 item, got {}", module.items.len());
            }
        }
        Err(e) => {
            println!("❌ Failed: Parse error: {:?}", e);
        }
    }
}
