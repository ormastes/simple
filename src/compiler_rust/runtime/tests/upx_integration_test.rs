//! Integration test for UPX auto-download functionality

use simple_runtime::compress::upx_download::{ensure_upx_available, find_upx_binary};

#[test]
#[ignore] // Ignore by default as it downloads from network
fn test_upx_auto_download() {
    // This test will download UPX if not found
    let result = ensure_upx_available();

    match result {
        Ok(path) => {
            println!("✓ UPX available at: {}", path.display());
            assert!(path.exists(), "UPX binary should exist at the returned path");

            // Verify it's executable
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                let metadata = std::fs::metadata(&path).unwrap();
                let permissions = metadata.permissions();
                assert!(permissions.mode() & 0o111 != 0, "UPX should be executable");
            }

            // Try to run it
            let output = std::process::Command::new(&path)
                .arg("--version")
                .output()
                .expect("Failed to run UPX");

            assert!(output.status.success(), "UPX --version should succeed");
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert!(
                stdout.contains("UPX") || stdout.contains("upx"),
                "UPX version output should contain 'UPX'"
            );

            println!("✓ UPX version: {}", stdout.lines().next().unwrap_or(""));
        }
        Err(e) => {
            panic!("Failed to ensure UPX is available: {}", e);
        }
    }
}

#[test]
fn test_find_upx_binary() {
    // This test should pass whether UPX is installed or not
    let result = find_upx_binary();

    match result {
        Some(path) => {
            println!("✓ UPX found at: {}", path.display());
        }
        None => {
            println!("✓ UPX not found (this is OK for this test)");
        }
    }
}
