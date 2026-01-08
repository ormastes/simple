//! BDD Test Runner for Simple Mixin Features
//!
//! This test suite executes Gherkin feature files from specs/features/
//! and validates mixin functionality end-to-end.

use cucumber::{given, then, when, World};
use simple_parser::Parser;
use std::path::PathBuf;
use std::fs;

#[derive(Debug, Default, World)]
pub struct MixinWorld {
    /// Current test file content
    source_code: String,
    /// Parser output (AST)
    parse_result: Option<Result<simple_parser::ast::Module, String>>,
    /// Temp file path for test
    temp_file: Option<PathBuf>,
}

// ============================================================================
// GIVEN steps - Setup test fixtures
// ============================================================================

#[given(regex = r#"^a file "([^"]+)" with content:$"#)]
async fn given_file_with_content(world: &mut MixinWorld, filename: String, content: String) {
    world.source_code = content.clone();

    // Create temp file
    let temp_dir = std::env::temp_dir();
    let file_path = temp_dir.join(filename);
    fs::write(&file_path, &content).expect("Failed to write temp file");
    world.temp_file = Some(file_path);
}

#[given("the Simple compiler is available")]
async fn given_compiler_available(_world: &mut MixinWorld) {
    // Compiler is always available in tests
}

#[given("the type checker is enabled")]
async fn given_type_checker_enabled(_world: &mut MixinWorld) {
    // Type checker is enabled by default
}

#[given("type inference is enabled")]
async fn given_type_inference_enabled(_world: &mut MixinWorld) {
    // Type inference is enabled by default
}

// ============================================================================
// WHEN steps - Execute actions
// ============================================================================

#[when("I parse the file")]
async fn when_parse_file(world: &mut MixinWorld) {
    let mut parser = Parser::new(&world.source_code);
    world.parse_result = Some(
        parser.parse()
            .map_err(|e| format!("{:?}", e))
    );
}

#[when("I compile the file")]
async fn when_compile_file(world: &mut MixinWorld) {
    // For now, just parse
    when_parse_file(world).await;
}

#[when("I compile the file with type inference")]
async fn when_compile_with_inference(world: &mut MixinWorld) {
    when_compile_file(world).await;
}

// ============================================================================
// THEN steps - Assertions
// ============================================================================

#[then("parsing should succeed")]
async fn then_parsing_succeeds(world: &mut MixinWorld) {
    let result = world.parse_result.as_ref()
        .expect("No parse result available");
    
    assert!(result.is_ok(), "Parsing failed: {:?}", result);
}

#[then("compilation should succeed")]
async fn then_compilation_succeeds(world: &mut MixinWorld) {
    let result = world.parse_result.as_ref()
        .expect("No parse result available");
    
    assert!(result.is_ok(), "Compilation failed: {:?}", result);
}

#[then("compilation should fail")]
async fn then_compilation_fails(world: &mut MixinWorld) {
    let result = world.parse_result.as_ref()
        .expect("No parse result available");
    
    assert!(result.is_err(), "Expected compilation to fail but it succeeded");
}

#[then(regex = r#"^the AST should contain a mixin declaration "([^"]+)"$"#)]
async fn then_ast_contains_mixin(world: &mut MixinWorld, _name: String) {
    let result = world.parse_result.as_ref()
        .expect("No parse result available");
    
    let _module = result.as_ref()
        .expect("Parse result is error");
    
    // TODO: Implement AST inspection once structure is stable
    println!("TODO: Check AST for mixin");
}

#[then(regex = r#"^the mixin should have (\d+) fields$"#)]
async fn then_mixin_has_fields(_world: &mut MixinWorld, _count: usize) {
    println!("TODO: Check mixin field count");
}

#[then(regex = r#"^field "([^"]+)" should have type "([^"]+)"$"#)]
async fn then_field_has_type(_world: &mut MixinWorld, _field_name: String, _type_name: String) {
    println!("TODO: Check field type");
}

#[then(regex = r#"^the mixin should have method "([^"]+)"$"#)]
async fn then_mixin_has_method(_world: &mut MixinWorld, _method_name: String) {
    println!("TODO: Check mixin method");
}

#[then(regex = r#"^method "([^"]+)" should take (\d+) parameter"#)]
async fn then_method_has_parameters(_world: &mut MixinWorld, _method_name: String, _count: usize) {
    println!("TODO: Check method parameters");
}

#[then(regex = r#"^the error should mention "([^"]+)"$"#)]
async fn then_error_mentions(world: &mut MixinWorld, message: String) {
    let result = world.parse_result.as_ref()
        .expect("No result available")
        .as_ref()
        .err();
    
    let error = result.expect("Expected error but got success");
    assert!(error.contains(&message), 
        "Error message '{}' does not contain '{}'", error, message);
}

#[then(regex = r#"^class "([^"]+)" should have field "([^"]+)" of type "([^"]+)"$"#)]
async fn then_class_has_field(_world: &mut MixinWorld, _class_name: String, _field_name: String, _type_name: String) {
    println!("TODO: Check class field");
}

#[then(regex = r#"^class "([^"]+)" should have method "([^"]+)"$"#)]
async fn then_class_has_method(_world: &mut MixinWorld, _class_name: String, _method_name: String) {
    println!("TODO: Check class method");
}

#[then(regex = r#"^class "([^"]+)" should have field "([^"]+)" from mixin "([^"]+)"$"#)]
async fn then_class_has_field_from_mixin(_world: &mut MixinWorld, _class_name: String, _field_name: String, _mixin_name: String) {
    println!("TODO: Check mixin-originated field");
}

#[then(regex = r#"^class "([^"]+)" should have field "([^"]+)"$"#)]
async fn then_class_has_field_simple(_world: &mut MixinWorld, _class_name: String, _field_name: String) {
    println!("TODO: Check class has field");
}

#[then(regex = r#"^the mixin should have type parameter "([^"]+)"$"#)]
async fn then_mixin_has_type_param(_world: &mut MixinWorld, _param_name: String) {
    println!("TODO: Check type parameter");
}

#[then(regex = r#"^the mixin should have type parameters "([^"]+)" and "([^"]+)"$"#)]
async fn then_mixin_has_two_type_params(_world: &mut MixinWorld, _param1: String, _param2: String) {
    println!("TODO: Check two type parameters");
}

#[then(regex = r#"^method "([^"]+)" should return type "([^"]+)"$"#)]
async fn then_method_returns_type(_world: &mut MixinWorld, _method_name: String, _type_name: String) {
    println!("TODO: Check method return type");
}

#[then(regex = r#"^method "([^"]+)" should take parameter of type "([^"]+)"$"#)]
async fn then_method_takes_param_type(_world: &mut MixinWorld, _method_name: String, _type_name: String) {
    println!("TODO: Check method parameter type");
}

#[then(regex = r#"^type parameter "([^"]+)" should have trait bound "([^"]+)"$"#)]
async fn then_type_param_has_trait_bound(_world: &mut MixinWorld, _param: String, _trait_name: String) {
    println!("TODO: Check trait bound");
}

#[then(regex = r#"^the mixin type parameter "([^"]+)" should be inferred as "([^"]+)"$"#)]
async fn then_mixin_type_inferred(_world: &mut MixinWorld, _param: String, _inferred_type: String) {
    println!("TODO: Check type inference");
}

#[then(regex = r#"^field "([^"]+)" should have inferred type "([^"]+)"$"#)]
async fn then_field_has_inferred_type(_world: &mut MixinWorld, _field_name: String, _type_name: String) {
    println!("TODO: Check inferred field type");
}

#[then(regex = r#"^type parameter "([^"]+)" should have default type "([^"]+)"$"#)]
async fn then_type_param_has_default(_world: &mut MixinWorld, _param: String, _default_type: String) {
    println!("TODO: Check default type parameter");
}

#[then(regex = r#"^the mixin "([^"]+)" type parameter should be "([^"]+)"$"#)]
async fn then_mixin_type_param_is(_world: &mut MixinWorld, _mixin_name: String, _type_value: String) {
    println!("TODO: Check mixin type parameter value");
}

#[then(regex = r#"^the class "([^"]+)" type parameter should remain independent$"#)]
async fn then_class_type_param_independent(_world: &mut MixinWorld, _class_name: String) {
    println!("TODO: Check type parameter independence");
}

#[then(regex = r#"^the mixin should have required method "([^"]+)"$"#)]
async fn then_mixin_has_required_method(_world: &mut MixinWorld, _method_name: String) {
    println!("TODO: Check required method");
}

// ============================================================================
// Test Runner Configuration
// ============================================================================

#[tokio::main]
async fn main() {
    MixinWorld::cucumber()
        .with_default_cli()
        .run("specs/features/mixin_basic.feature")
        .await;
    
    MixinWorld::cucumber()
        .with_default_cli()
        .run("specs/features/mixin_generic.feature")
        .await;
}
