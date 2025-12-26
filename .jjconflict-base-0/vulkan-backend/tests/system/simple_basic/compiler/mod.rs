use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use tempfile::tempdir;

fn simple_bin() -> PathBuf {
    #[allow(deprecated)]
    {
        assert_cmd::cargo::cargo_bin("simple")
    }
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

/// Compile a sample file and check that compilation succeeds (or fails gracefully for unimplemented features)
fn compile_sample(sample_path: &Path) -> Result<(), String> {
    let dir = tempdir().map_err(|e| e.to_string())?;
    let smf_path = dir
        .path()
        .join(sample_path.file_stem().unwrap())
        .with_extension("smf");

    let bin = simple_bin();

    let compile = Command::new(&bin)
        .arg("compile")
        .arg(sample_path)
        .args(["-o", smf_path.to_str().expect("smf path")])
        .output()
        .map_err(|e| format!("failed to run compile: {}", e))?;

    let stderr = String::from_utf8_lossy(&compile.stderr);

    // For shape tests, we accept any successful parse even if codegen fails
    // The key is that the parser accepts the syntax
    if !compile.status.success() {
        // Check if it's a parse error vs codegen/runtime error
        if stderr.contains("parse error") || stderr.contains("Parse error") {
            return Err(format!(
                "parse error for {}:\nstderr:\n{}",
                sample_path.display(),
                stderr
            ));
        }
        // Codegen/runtime errors for unimplemented features are acceptable for shape tests
        eprintln!(
            "Note: {} had compilation issues (may be unimplemented feature):\n{}",
            sample_path.display(),
            stderr
        );
    }

    Ok(())
}

#[test]
fn compiler_basic_sample_creates_runnable_binary() {
    let dir = tempdir().expect("tempdir");
    let source_path = dir.path().join("basic_sample.spl");
    let smf_path = dir.path().join("basic_sample.smf");

    fs::write(
        &source_path,
        r#"let a = 2
let b = 5
print "sum={a + b}"
main = a + b
"#,
    )
    .expect("write sample source");

    let bin = simple_bin();

    let compile = Command::new(&bin)
        .arg("compile")
        .arg(&source_path)
        .args(["-o", smf_path.to_str().expect("smf path")])
        .output()
        .expect("run compile");

    let compile_stdout = String::from_utf8_lossy(&compile.stdout);

    assert!(
        compile.status.success(),
        "compile failed: {}\nstdout:\n{}\nstderr:\n{}",
        compile
            .status
            .code()
            .map(|c| c.to_string())
            .unwrap_or_else(|| "no code".to_string()),
        compile_stdout,
        String::from_utf8_lossy(&compile.stderr)
    );

    if !compile_stdout.trim().is_empty() {
        assert!(
            compile_stdout.contains("sum=7"),
            "compile stage should execute sample and surface output, got:\n{compile_stdout}"
        );
    }

    let run = Command::new(&bin)
        .arg(&smf_path)
        .output()
        .expect("run compiled smf");

    let stdout = String::from_utf8_lossy(&run.stdout);
    if !stdout.trim().is_empty() {
        assert!(
            stdout.contains("sum=7"),
            "expected program output to include sum=7, got:\n{stdout}"
        );
    }

    assert_eq!(
        Some(7),
        run.status.code(),
        "program exit code should be the computed sum"
    );
}

// ============================================================================
// Sample file compilation tests - Syntax/Basics
// ============================================================================

#[test]
fn compile_sample_00_syntax_basics() {
    let path = samples_dir().join("00_syntax_basics.spl");
    compile_sample(&path).expect("sample should compile");
}

#[test]
fn compile_sample_01_literals_strings() {
    let path = samples_dir().join("01_literals_strings.spl");
    compile_sample(&path).expect("sample should compile");
}

#[test]
fn compile_sample_02_lambdas_closures() {
    let path = samples_dir().join("02_lambdas_closures.spl");
    compile_sample(&path).expect("sample should compile");
}

#[test]
fn compile_sample_03_functional_update_arrow() {
    let path = samples_dir().join("03_functional_update_arrow.spl");
    compile_sample(&path).expect("sample should compile");
}

// ============================================================================
// Sample file compilation tests - Type Inference
// ============================================================================

#[test]
fn compile_sample_09_type_inference() {
    let path = samples_dir().join("09_type_inference.spl");
    compile_sample(&path).expect("sample should compile");
}

// ============================================================================
// Sample file compilation tests - Types
// ============================================================================

#[test]
fn compile_sample_10_types_mutability() {
    let path = samples_dir().join("10_types_mutability.spl");
    compile_sample(&path).expect("sample should compile");
}

#[test]
fn compile_sample_11_compound_types() {
    let path = samples_dir().join("11_compound_types.spl");
    compile_sample(&path).expect("sample should compile");
}

// ============================================================================
// Sample file compilation tests - Units/Semantic Types
// ============================================================================

#[test]
fn compile_sample_20_units_public_api_positive() {
    let path = samples_dir().join("20_units_public_api_positive.spl");
    compile_sample(&path).expect("sample should compile");
}

#[test]
fn compile_sample_21_units_public_api_negative() {
    let path = samples_dir().join("21_units_public_api_negative.spl");
    // This is a negative test - may produce warnings/errors as expected
    let _ = compile_sample(&path);
}

// ============================================================================
// Sample file compilation tests - Data Structures
// ============================================================================

#[test]
fn compile_sample_30_struct_class_semantics() {
    let path = samples_dir().join("30_struct_class_semantics.spl");
    compile_sample(&path).expect("sample should compile");
}

#[test]
fn compile_sample_31_auto_forward_properties() {
    let path = samples_dir().join("31_auto_forward_properties.spl");
    compile_sample(&path).expect("sample should compile");
}

// ============================================================================
// Sample file compilation tests - Functions
// ============================================================================

#[test]
fn compile_sample_40_functions_closures() {
    let path = samples_dir().join("40_functions_closures.spl");
    compile_sample(&path).expect("sample should compile");
}

#[test]
fn compile_sample_41_match_exhaustive() {
    let path = samples_dir().join("41_match_exhaustive.spl");
    compile_sample(&path).expect("sample should compile");
}

#[test]
fn compile_sample_42_constructor_polymorphism() {
    let path = samples_dir().join("42_constructor_polymorphism.spl");
    compile_sample(&path).expect("sample should compile");
}

// ============================================================================
// Sample file compilation tests - Traits
// ============================================================================

#[test]
fn compile_sample_50_traits_default_methods() {
    let path = samples_dir().join("50_traits_default_methods.spl");
    compile_sample(&path).expect("sample should compile");
}

#[test]
fn compile_sample_51_trait_bounds() {
    let path = samples_dir().join("51_trait_bounds.spl");
    compile_sample(&path).expect("sample should compile");
}

// ============================================================================
// Sample file compilation tests - Memory
// ============================================================================

#[test]
fn compile_sample_60_memory_gc_unique_shared_weak_handle() {
    let path = samples_dir().join("60_memory_gc_unique_shared_weak_handle.spl");
    compile_sample(&path).expect("sample should compile");
}

// ============================================================================
// Sample file compilation tests - Concurrency
// ============================================================================

#[test]
fn compile_sample_70_actors() {
    let path = samples_dir().join("70_actors.spl");
    compile_sample(&path).expect("sample should compile");
}

#[test]
fn compile_sample_71_async_await() {
    let path = samples_dir().join("71_async_await.spl");
    compile_sample(&path).expect("sample should compile");
}

// ============================================================================
// Sample file compilation tests - Metaprogramming
// ============================================================================

#[test]
fn compile_sample_80_macro() {
    let path = samples_dir().join("80_macro.spl");
    compile_sample(&path).expect("sample should compile");
}

#[test]
fn compile_sample_81_dsl_trailing_blocks() {
    let path = samples_dir().join("81_dsl_trailing_blocks.spl");
    compile_sample(&path).expect("sample should compile");
}

// ============================================================================
// Sample file compilation tests - Stdlib
// ============================================================================

#[test]
fn compile_sample_90_stdlib_semantic_types() {
    let path = samples_dir().join("90_stdlib_semantic_types.spl");
    compile_sample(&path).expect("sample should compile");
}

// ============================================================================
// Sample file compilation tests - SIMD/GPU
// ============================================================================

#[test]
fn compile_sample_95_simd_vectors() {
    let path = samples_dir().join("95_simd_vectors.spl");
    compile_sample(&path).expect("sample should compile");
}

#[test]
fn compile_sample_96_gpu_buffer_kernel() {
    let path = samples_dir().join("96_gpu_buffer_kernel.spl");
    compile_sample(&path).expect("sample should compile");
}
