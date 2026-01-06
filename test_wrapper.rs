// Test wrapper to reproduce the cargo test issue
use std::path::Path;

// Simulate the dependencies
fn main() {
    // This simulates what run_test_file does
    let path = Path::new("test_json_minimal.spl");

    // Clear module cache (this is what cargo test wrapper does)
    simple_compiler::interpreter::clear_module_cache();

    // Create interpreter
    let interpreter = simple_driver::Interpreter::new();
    let config = simple_driver::RunConfig {
        capture_output: true,
        ..Default::default()
    };

    // Run the file
    match interpreter.run_file(path, config) {
        Ok(result) => {
            println!("SUCCESS!");
            println!("stdout: {}", result.stdout);
            println!("stderr: {}", result.stderr);
            println!("exit_code: {}", result.exit_code);
        }
        Err(e) => {
            println!("ERROR!");
            println!("error: {}", e);
        }
    }
}
