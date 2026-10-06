//! Date.now uses epoch milliseconds through the registered interpreter extern.
use simple_compiler::interpreter;
use simple_parser::Parser;
use std::time::{SystemTime, UNIX_EPOCH};
#[test]
fn registered_unix_millis_uses_wall_clock_epoch_and_units() {
    let before = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_millis();
    let source = format!("extern fn rt_time_now_unix_millis() -> i64\nval observed = rt_time_now_unix_millis()\nmain = if observed >= {before} and observed <= {}: 0 else: 1\n", before + 30000);
    let module = Parser::new(&source).parse().unwrap();
    assert_eq!(interpreter::evaluate_module(&module.items).unwrap(), 0);
}
