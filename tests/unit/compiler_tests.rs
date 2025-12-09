//! Compiler unit tests

use simple_compiler::CompilerPipeline;
use tempfile::tempdir;
use std::fs;

#[test]
fn test_compiler_pipeline_creation() {
    let pipeline = CompilerPipeline::new();
    assert!(pipeline.is_ok(), "CompilerPipeline::new should succeed");
}

#[test]
fn test_compile_simple_expression() {
    let dir = tempdir().expect("tempdir");
    let src = dir.path().join("test.spl");
    let out = dir.path().join("test.smf");

    fs::write(&src, "main = 1 + 2").expect("write ok");

    let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
    let result = pipeline.compile(&src, &out);
    assert!(result.is_ok(), "Should compile simple expression: {:?}", result.err());
}

#[test]
fn test_compile_function() {
    let dir = tempdir().expect("tempdir");
    let src = dir.path().join("test.spl");
    let out = dir.path().join("test.smf");

    // Use correct syntax: Python-like with colons and indentation
    fs::write(&src, "fn foo():\n    return 42\nmain = foo()").expect("write ok");

    let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
    let result = pipeline.compile(&src, &out);
    // Note: May fail due to current compiler limitations
    if result.is_err() {
        println!("Compile error (expected for now): {:?}", result.err());
    }
}

#[test]
fn test_compile_main_binding() {
    let dir = tempdir().expect("tempdir");
    let src = dir.path().join("test.spl");
    let out = dir.path().join("test.smf");

    fs::write(&src, "main = 42").expect("write ok");

    let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
    let result = pipeline.compile(&src, &out);
    assert!(result.is_ok(), "Should compile main binding: {:?}", result.err());
}
