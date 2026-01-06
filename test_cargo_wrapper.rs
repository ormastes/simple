use std::path::Path;

fn main() {
    use simple_driver::{Interpreter, RunConfig};
    simple_compiler::interpreter::clear_module_cache();
    let path = Path::new("test_json_two_tests.spl");
    let interpreter = Interpreter::new();
    let config = RunConfig { capture_output: true, ..Default::default() };
    match interpreter.run_file(path, config) {
        Ok(result) => println!("OK: exit={}\nstdout:\n{}", result.exit_code, result.stdout),
        Err(e) => println!("ERR: {}", e),
    }
}
