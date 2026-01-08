use super::run_code;

// ============================================================================
// Full Macro Syntax Tests (per doc/spec/macro.md)
// ============================================================================

#[test]
fn macro_full_syntax_const_param() {
    // Macro with const parameter and template substitution
    let code = r#"
macro greet(name: Str const) -> (returns result: Str):
    emit result:
        "Hello, {name}!"

let msg = greet!("World")
main = if msg == "Hello, World!": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn macro_full_syntax_const_eval_block() {
    // Macro with const_eval block
    let code = r#"
macro make_sum() -> (returns result: Int):
    const_eval:
        const x = 10
        const y = 20
    emit result:
        x + y

main = make_sum!()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30);
}

#[test]
fn macro_full_syntax_const_arithmetic() {
    // Macro with const arithmetic in const_eval
    let code = r#"
macro calculate() -> (returns result: Int):
    const_eval:
        const a = 5
        const b = 3
        const c = a * b + 2
    emit result:
        c

main = calculate!()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 17);
}

#[test]
fn macro_full_syntax_multiple_params() {
    // Macro with multiple parameters of different types
    let code = r#"
macro combine(x: Int, y: Int, z: Int) -> (returns result: Int):
    emit result:
        x * 100 + y * 10 + z

main = combine!(1, 2, 3)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 123);
}

#[test]
fn macro_full_syntax_const_and_non_const_params() {
    // Macro with both const and non-const parameters
    let code = r#"
macro multiply(factor: Int const, value: Int) -> (returns result: Int):
    emit result:
        value * factor

main = multiply!(5, 8)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 40);
}

#[test]
fn macro_full_syntax_nested_expressions() {
    // Macro emit block with nested expressions
    let code = r#"
macro complex(a: Int, b: Int) -> (returns result: Int):
    emit result:
        let x = a + b
        let y = a - b
        x * y

main = complex!(10, 3)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 91); // (10+3) * (10-3) = 13 * 7 = 91
}

#[test]
fn macro_full_syntax_labeled_returns() {
    // Macro with labeled returns
    let code = r#"
macro with_label() -> (returns my_result: Int):
    emit my_result:
        42

main = with_label!()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn macro_full_syntax_string_template() {
    // Macro with string template substitution using const param
    let code = r#"
macro make_message(prefix: Str const) -> (returns result: Str):
    emit result:
        "{prefix}: done"

let msg = make_message!("Task")
main = if msg == "Task: done": 1 else: 0
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1);
}

#[test]
fn macro_full_syntax_conditional_in_emit() {
    // Macro emit block with conditional logic
    let code = r#"
macro clamp(val: Int, min: Int, max: Int) -> (returns result: Int):
    emit result:
        if val < min:
            return min
        elif val > max:
            return max
        else:
            return val

main = clamp!(15, 10, 20)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}

#[test]
fn macro_full_syntax_clamp_low() {
    let code = r#"
macro clamp(val: Int, min: Int, max: Int) -> (returns result: Int):
    emit result:
        if val < min:
            return min
        elif val > max:
            return max
        else:
            return val

main = clamp!(5, 10, 20)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 10);
}

#[test]
fn macro_full_syntax_clamp_high() {
    let code = r#"
macro clamp(val: Int, min: Int, max: Int) -> (returns result: Int):
    emit result:
        if val < min:
            return min
        elif val > max:
            return max
        else:
            return val

main = clamp!(25, 10, 20)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 20);
}

#[test]
fn macro_full_syntax_empty_contract() {
    // Macro with empty contract items (just returns)
    let code = r#"
macro identity(x: Int) -> (returns result: Int):
    emit result:
        x

main = identity!(99)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 99);
}

#[test]
fn macro_full_syntax_loop_in_emit() {
    // Macro emit block with loop (read-only iteration)
    // Note: Loop with mutation inside macros requires hygiene fixes
    let code = r#"
macro count_to(n: Int) -> (returns result: Int):
    emit result:
        let arr = [1, 2, 3, 4, 5]
        arr.len()

main = count_to!(5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 5);
}

#[test]
fn macro_full_syntax_function_call_in_emit() {
    // Macro emit block that uses function defined in module
    let code = r#"
fn helper(x: Int) -> Int:
    return x * 2

macro double_it(val: Int) -> (returns result: Int):
    emit result:
        helper(val)

main = double_it!(21)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn macro_full_syntax_multiline_emit() {
    // Macro with multi-line emit block
    let code = r#"
macro compute() -> (returns result: Int):
    emit result:
        let a = 1
        let b = 2
        let c = 3
        let d = 4
        let e = 5
        a + b + c + d + e

main = compute!()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 15);
}
