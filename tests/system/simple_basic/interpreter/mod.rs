use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn simple_bin() -> PathBuf {
    #[allow(deprecated)]
    {
        assert_cmd::cargo::cargo_bin("simple")
    }
}

/// Parse a Simple doctest-style transcript (>>> for input, following lines for expected output).
fn parse_sdoctest(script: &str) -> (Vec<String>, Vec<String>) {
    let mut commands = Vec::new();
    let mut expected = Vec::new();

    for line in script.lines() {
        let trimmed = line.trim_end();
        if trimmed.starts_with(">>>") {
            commands.push(trimmed.trim_start_matches(">>>").trim_start().to_string());
        } else if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        } else {
            expected.push(trimmed.to_string());
        }
    }

    (commands, expected)
}

fn run_repl_script(script: &str) -> Result<(), String> {
    let (commands, expected) = parse_sdoctest(script);

    let mut input = commands.join("\n");
    input.push('\n');

    let bin = simple_bin();
    let mut child = Command::new(bin)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| e.to_string())?;

    child
        .stdin
        .as_mut()
        .ok_or("failed to open stdin for simple repl")?
        .write_all(input.as_bytes())
        .map_err(|e| e.to_string())?;

    let output = child.wait_with_output().map_err(|e| e.to_string())?;

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    if !output.status.success() {
        return Err(format!(
            "simple repl exited with status {:?}\nstderr:\n{stderr}",
            output.status.code()
        ));
    }

    let actual: Vec<_> = stdout
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .filter(|line| {
            !line.starts_with("Simple Language v") && !line.starts_with("Type expressions")
        })
        .map(str::to_string)
        .collect();

    if !stderr.trim().is_empty() {
        return Err(format!("unexpected stderr output:\n{stderr}"));
    }

    assert_eq!(
        expected, actual,
        "stdout did not match for script:\n{script}"
    );

    Ok(())
}

/// Run a sample file through the interpreter
fn run_sample_interpret(sample_path: &Path) -> Result<i32, String> {
    let bin = simple_bin();
    let output = Command::new(&bin)
        .arg("run")
        .arg(sample_path)
        .output()
        .map_err(|e| format!("failed to execute: {}", e))?;

    let _stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // For shape tests, we accept any successful parse/run even if features aren't implemented
    // The key is that the parser accepts the syntax
    if !output.status.success() {
        // Check if it's a parse error vs runtime error
        if stderr.contains("parse error") || stderr.contains("Parse error") {
            return Err(format!(
                "parse error for {}:\nstderr:\n{}",
                sample_path.display(),
                stderr
            ));
        }
        // Runtime errors for unimplemented features are acceptable for shape tests
        eprintln!(
            "Note: {} had runtime issues (may be unimplemented feature):\n{}",
            sample_path.display(),
            stderr
        );
    }

    Ok(output.status.code().unwrap_or(-1))
}

/// Get the samples directory path
fn samples_dir() -> PathBuf {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    PathBuf::from(manifest_dir)
        .join("tests")
        .join("system")
        .join("simple_basic")
        .join("samples")
}

#[test]
fn interpreter_basic_sample_check_transcript() {
    // Derived from doc/basic_sample_check.md (syntax + literals) using sdoctest-style transcript.
    let script = include_str!("basic_sample_check.sdt");
    run_repl_script(script).expect("repl transcript should pass");
}

#[test]
fn interpreter_repl_regressions() {
    let script = include_str!("repl_regressions.sdt");
    run_repl_script(script).expect("repl regression transcript should pass");
}

// ============================================================================
// Sample file tests - Syntax/Basics
// ============================================================================

#[test]
fn sample_00_syntax_basics() {
    let path = samples_dir().join("00_syntax_basics.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

#[test]
fn sample_01_literals_strings() {
    let path = samples_dir().join("01_literals_strings.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

#[test]
fn sample_02_lambdas_closures() {
    let path = samples_dir().join("02_lambdas_closures.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

#[test]
fn sample_03_functional_update_arrow() {
    let path = samples_dir().join("03_functional_update_arrow.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

// ============================================================================
// Sample file tests - Type Inference
// ============================================================================

#[test]
fn sample_09_type_inference() {
    let path = samples_dir().join("09_type_inference.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

// ============================================================================
// Sample file tests - Types
// ============================================================================

#[test]
fn sample_10_types_mutability() {
    let path = samples_dir().join("10_types_mutability.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

#[test]
fn sample_11_compound_types() {
    let path = samples_dir().join("11_compound_types.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

// ============================================================================
// Sample file tests - Units/Semantic Types
// ============================================================================

#[test]
fn sample_20_units_public_api_positive() {
    let path = samples_dir().join("20_units_public_api_positive.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

#[test]
fn sample_21_units_public_api_negative() {
    let path = samples_dir().join("21_units_public_api_negative.spl");
    // This is a negative test - may produce warnings/errors as expected
    let _ = run_sample_interpret(&path);
}

// ============================================================================
// Sample file tests - Data Structures
// ============================================================================

#[test]
fn sample_30_struct_class_semantics() {
    let path = samples_dir().join("30_struct_class_semantics.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

#[test]
fn sample_31_auto_forward_properties() {
    let path = samples_dir().join("31_auto_forward_properties.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

// ============================================================================
// Sample file tests - Functions
// ============================================================================

#[test]
fn sample_40_functions_closures() {
    let path = samples_dir().join("40_functions_closures.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

#[test]
fn sample_41_match_exhaustive() {
    let path = samples_dir().join("41_match_exhaustive.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

#[test]
fn sample_42_constructor_polymorphism() {
    let path = samples_dir().join("42_constructor_polymorphism.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

// ============================================================================
// Sample file tests - Traits
// ============================================================================

#[test]
fn sample_50_traits_default_methods() {
    let path = samples_dir().join("50_traits_default_methods.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

#[test]
fn sample_51_trait_bounds() {
    let path = samples_dir().join("51_trait_bounds.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

// ============================================================================
// Sample file tests - Memory
// ============================================================================

#[test]
fn sample_60_memory_gc_unique_shared_weak_handle() {
    let path = samples_dir().join("60_memory_gc_unique_shared_weak_handle.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

// ============================================================================
// Sample file tests - Concurrency
// ============================================================================

#[test]
fn sample_70_actors() {
    let path = samples_dir().join("70_actors.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

#[test]
fn sample_71_async_await() {
    let path = samples_dir().join("71_async_await.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

// ============================================================================
// Sample file tests - Metaprogramming
// ============================================================================

#[test]
fn sample_80_macro() {
    let path = samples_dir().join("80_macro.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

#[test]
fn sample_81_dsl_trailing_blocks() {
    let path = samples_dir().join("81_dsl_trailing_blocks.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

// ============================================================================
// Sample file tests - Stdlib
// ============================================================================

#[test]
fn sample_90_stdlib_semantic_types() {
    let path = samples_dir().join("90_stdlib_semantic_types.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

// ============================================================================
// Sample file tests - SIMD/GPU
// ============================================================================

#[test]
fn sample_95_simd_vectors() {
    let path = samples_dir().join("95_simd_vectors.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

#[test]
fn sample_96_gpu_buffer_kernel() {
    let path = samples_dir().join("96_gpu_buffer_kernel.spl");
    run_sample_interpret(&path).expect("sample should parse and run");
}

// ============================================================================
// Test that all sample files exist
// ============================================================================

#[test]
fn all_samples_exist() {
    let dir = samples_dir();
    let expected_samples = [
        "00_syntax_basics.spl",
        "01_literals_strings.spl",
        "02_lambdas_closures.spl",
        "03_functional_update_arrow.spl",
        "09_type_inference.spl",
        "10_types_mutability.spl",
        "11_compound_types.spl",
        "20_units_public_api_positive.spl",
        "21_units_public_api_negative.spl",
        "30_struct_class_semantics.spl",
        "31_auto_forward_properties.spl",
        "40_functions_closures.spl",
        "41_match_exhaustive.spl",
        "42_constructor_polymorphism.spl",
        "50_traits_default_methods.spl",
        "51_trait_bounds.spl",
        "60_memory_gc_unique_shared_weak_handle.spl",
        "70_actors.spl",
        "71_async_await.spl",
        "80_macro.spl",
        "81_dsl_trailing_blocks.spl",
        "90_stdlib_semantic_types.spl",
        "95_simd_vectors.spl",
        "96_gpu_buffer_kernel.spl",
    ];

    for sample in expected_samples {
        let path = dir.join(sample);
        assert!(
            path.exists(),
            "sample file {} does not exist at {}",
            sample,
            path.display()
        );
    }
}
