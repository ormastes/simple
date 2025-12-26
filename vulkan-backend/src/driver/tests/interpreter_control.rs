#![allow(unused_imports)]

//! Interpreter tests - control

use simple_driver::interpreter::{run_code, Interpreter, RunConfig};

#[test]
fn interpreter_if_else() {
    let code = r#"
let x = 10
main = if x > 5: 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn interpreter_while_loop() {
    let code = r#"
sum = 0
i = 0
while i < 5:
    sum = sum + i
    i = i + 1
main = sum
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10); // 0+1+2+3+4 = 10
}

#[test]
fn interpreter_for_loop() {
    let code = r#"
sum = 0
for i in range(1, 5):
    sum = sum + i
main = sum
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10); // 1+2+3+4 = 10
}

#[test]
fn interpreter_match_tuple() {
    let code = r#"
t = (1, 2)
match t:
    (1, x) =>
        main = x * 10
    _ =>
        main = 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 20);
}

#[test]
fn interpreter_match_array() {
    let code = r#"
arr = [5, 10]
match arr:
    [a, b] =>
        main = a + b
    _ =>
        main = 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

// ============= Global len() Function =============
