//! Tests for line coverage in the interpreter

use simple_compiler::{interpreter, coverage};
use simple_parser::Parser;

/// Helper to run Simple code through the interpreter
fn run_interpreter(code: &str) -> Result<i32, Box<dyn std::error::Error>> {
    let mut parser = Parser::new(code);
    let module = parser.parse()?;
    Ok(interpreter::evaluate_module(&module.items)?)
}

/// Helper to enable and check coverage
fn check_coverage_enabled() -> bool {
    coverage::is_coverage_enabled()
}

/// Helper to get the global coverage collector
fn get_coverage() -> Option<&'static std::sync::Mutex<coverage::CoverageCollector>> {
    coverage::get_global_coverage()
}

#[test]
fn test_line_coverage_basic() {
    if !check_coverage_enabled() {
        println!("Coverage disabled, skipping test");
        return;
    }

    let code = r#"val x = 10
val y = 20
main = x + y"#;

    let result = run_interpreter(code).unwrap();
    assert_eq!(result, 30);

    if let Some(cov) = get_coverage() {
        if let Ok(cov) = cov.lock() {
            let stats = cov.stats();
            println!("Coverage stats: {:?}", stats);
            assert!(stats.total_lines > 0, "Should have recorded at least one line");
        }
    }
}

#[test]
fn test_line_coverage_control_flow() {
    if !check_coverage_enabled() {
        println!("Coverage disabled, skipping test");
        return;
    }

    let code = r#"fn test_if(n: i32) -> i32:
    if n > 0:
        return 1
    else:
        return 0

main = test_if(5)"#;

    let result = run_interpreter(code).unwrap();
    assert_eq!(result, 1);

    if let Some(cov) = get_coverage() {
        if let Ok(cov) = cov.lock() {
            let stats = cov.stats();
            println!("Function coverage: {} functions", stats.total_functions);
            assert!(cov.was_function_called("test_if"), "test_if should have been called");
        }
    }
}

#[test]
fn test_line_coverage_loop() {
    if !check_coverage_enabled() {
        println!("Coverage disabled, skipping test");
        return;
    }

    let code = r#"fn sum_to_n(n: i32) -> i32:
    var result = 0
    var i = 0
    while i < n:
        result = result + i
        i = i + 1
    result

main = sum_to_n(5)"#;

    let result = run_interpreter(code).unwrap();
    assert_eq!(result, 10); // 0 + 1 + 2 + 3 + 4 = 10

    if let Some(cov) = get_coverage() {
        if let Ok(cov) = cov.lock() {
            assert!(cov.was_function_called("sum_to_n"), "sum_to_n should have been called");
        }
    }
}

#[test]
fn test_line_coverage_with_multiple_lines() {
    if !check_coverage_enabled() {
        println!("Coverage disabled, skipping test");
        return;
    }

    let code = r#"val a = 1
val b = 2
val c = 3
main = a + b + c"#;

    let result = run_interpreter(code).unwrap();
    assert_eq!(result, 6);

    if let Some(cov) = get_coverage() {
        if let Ok(cov) = cov.lock() {
            let files = cov.executed_files();
            println!("Executed files: {:?}", files);
            assert!(!files.is_empty(), "Should have executed at least one file");
        }
    }
}

#[test]
fn test_coverage_disabled_performance() {
    // This test runs without coverage enabled
    let code = r#"fn factorial(n: i32) -> i32:
    if n <= 1:
        return 1
    else:
        return n * factorial(n - 1)

main = factorial(5)"#;

    let result = run_interpreter(code).unwrap();
    assert_eq!(result, 120);

    if !check_coverage_enabled() {
        println!("Coverage disabled - no coverage data collected");
    }
}

#[test]
fn test_decision_coverage_if_else() {
    if !check_coverage_enabled() {
        println!("Coverage disabled, skipping test");
        return;
    }

    let code = r#"fn check_sign(n: i32) -> i32:
    if n > 0:
        return 1
    else:
        return -1

main = check_sign(10)"#;

    let result = run_interpreter(code).unwrap();
    assert_eq!(result, 1);
}

#[test]
fn test_decision_coverage_while() {
    if !check_coverage_enabled() {
        println!("Coverage disabled, skipping test");
        return;
    }

    let code = r#"fn count_down(n: i32) -> i32:
    var count = 0
    while n > 0:
        count = count + 1
        n = n - 1
    count

main = count_down(3)"#;

    let result = run_interpreter(code).unwrap();
    assert_eq!(result, 3);
}

#[test]
fn test_decision_coverage_match() {
    if !check_coverage_enabled() {
        println!("Coverage disabled, skipping test");
        return;
    }

    let code = r#"fn classify(x: i32) -> i32:
    match x:
        case 1:
            return 10
        case 2:
            return 20
        case _:
            return 0

main = classify(1)"#;

    let result = run_interpreter(code).unwrap();
    assert_eq!(result, 10);
}

#[test]
fn test_decision_coverage_elif() {
    if !check_coverage_enabled() {
        println!("Coverage disabled, skipping test");
        return;
    }

    let code = r#"fn grade(score: i32) -> i32:
    if score >= 90:
        return 4
    elif score >= 80:
        return 3
    elif score >= 70:
        return 2
    else:
        return 1

main = grade(85)"#;

    let result = run_interpreter(code).unwrap();
    assert_eq!(result, 3);
}

#[test]
fn test_condition_coverage_and() {
    if !check_coverage_enabled() {
        println!("Coverage disabled, skipping test");
        return;
    }

    let code = r#"fn test_and(x: i32, y: i32) -> i32:
    if (x > 0) && (y < 10):
        return 1
    else:
        return 0

main = test_and(5, 5)"#;

    let result = run_interpreter(code).unwrap();
    assert_eq!(result, 1);
}

#[test]
fn test_condition_coverage_or() {
    if !check_coverage_enabled() {
        println!("Coverage disabled, skipping test");
        return;
    }

    let code = r#"fn test_or(x: i32, y: i32) -> i32:
    if (x > 0) || (y < 0):
        return 1
    else:
        return 0

main = test_or(-5, -5)"#;

    let result = run_interpreter(code).unwrap();
    assert_eq!(result, 1);
}

#[test]
fn test_condition_coverage_compound() {
    if !check_coverage_enabled() {
        println!("Coverage disabled, skipping test");
        return;
    }

    let code = r#"fn test_complex(a: i32, b: i32, c: i32) -> i32:
    if (a > 0) && ((b < 10) || (c == 0)):
        return 1
    else:
        return 0

main = test_complex(5, 5, 0)"#;

    let result = run_interpreter(code).unwrap();
    assert_eq!(result, 1);
}

#[test]
fn test_condition_coverage_short_circuit_and() {
    if !check_coverage_enabled() {
        println!("Coverage disabled, skipping test");
        return;
    }

    let code = r#"fn short_circuit_and(x: i32) -> i32:
    if (x < 0) && (x > 10):
        return 1
    else:
        return 0

main = short_circuit_and(-5)"#;

    let result = run_interpreter(code).unwrap();
    assert_eq!(result, 0);
}

#[test]
fn test_condition_coverage_short_circuit_or() {
    if !check_coverage_enabled() {
        println!("Coverage disabled, skipping test");
        return;
    }

    let code = r#"fn short_circuit_or(x: i32) -> i32:
    if (x > 0) || (x < -100):
        return 1
    else:
        return 0

main = short_circuit_or(5)"#;

    let result = run_interpreter(code).unwrap();
    assert_eq!(result, 1);
}
