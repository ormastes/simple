//! Test UPX compression with auto-download

use simple_runtime::compress::upx::{compress_file, is_compressed, CompressionLevel};
use std::fs;
use std::process::Command;
use tempfile::TempDir;

#[test]
#[ignore] // Ignore by default as it uses auto-downloaded UPX
fn test_compress_with_auto_download() {
    let temp_dir = TempDir::new().expect("Failed to create temp directory");

    // Create a simple test binary
    let test_src = temp_dir.path().join("test.rs");
    fs::write(
        &test_src,
        r#"
        fn main() {
            println!("Hello from compressed binary!");
        }
        "#,
    )
    .expect("Failed to write test source");

    // Compile it
    let test_binary = temp_dir.path().join("test_binary");
    let output = Command::new("rustc")
        .arg(&test_src)
        .arg("-o")
        .arg(&test_binary)
        .output()
        .expect("Failed to compile test binary");

    assert!(output.status.success(), "Compilation failed");
    assert!(test_binary.exists(), "Test binary should exist");

    let original_size = fs::metadata(&test_binary).expect("Failed to get metadata").len();

    println!("✓ Test binary created: {} bytes", original_size);

    // Compress it (should auto-download UPX if needed)
    let result = compress_file(
        test_binary.to_str().unwrap(),
        None, // In-place compression
        CompressionLevel::Best,
    );

    match result {
        Ok(output_path) => {
            println!("✓ Compression succeeded: {}", output_path);

            // Verify it's compressed
            let is_upx_compressed = is_compressed(output_path.as_str()).expect("Failed to check if compressed");
            assert!(is_upx_compressed, "Binary should be UPX-compressed");

            let compressed_size = fs::metadata(&test_binary).expect("Failed to get metadata").len();
            let ratio = original_size as f64 / compressed_size as f64;

            println!(
                "✓ Compressed: {} bytes -> {} bytes ({}x)",
                original_size, compressed_size, ratio
            );

            // Verify it still runs
            let run_output = Command::new(&test_binary)
                .output()
                .expect("Failed to run compressed binary");

            assert!(run_output.status.success(), "Compressed binary should run successfully");

            let stdout = String::from_utf8_lossy(&run_output.stdout);
            assert!(
                stdout.contains("Hello from compressed binary!"),
                "Compressed binary should produce correct output"
            );

            println!("✓ Compressed binary runs correctly");
        }
        Err(e) => {
            panic!("Compression failed: {}", e);
        }
    }
}
