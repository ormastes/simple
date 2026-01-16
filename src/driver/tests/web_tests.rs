// End-to-end tests for Simple web framework
// Tests: build, serve, init, optimization, hydration
// NOTE: These tests are disabled because cli module is not public in lib.rs
// They test planned web framework features that require cli module access.

#![cfg(feature = "web_tests")]

use std::fs;
use std::path::PathBuf;
use tempfile::TempDir;

#[cfg(test)]
mod web_e2e_tests {
    use super::*;
    // TODO: [driver][P3] Enable when cli module is public
    // use simple_driver::cli::web::{web_build, web_init, WebBuildOptions};

    /// Test helper: create temp directory
    fn setup_temp_dir() -> TempDir {
        TempDir::new().expect("Failed to create temp dir")
    }

    /// Test helper: create a simple .sui file
    fn create_simple_sui_file(dir: &TempDir, name: &str, content: &str) -> PathBuf {
        let file_path = dir.path().join(name);
        fs::write(&file_path, content).expect("Failed to write .sui file");
        file_path
    }

    #[test]
    fn test_web_build_basic() {
        let temp_dir = setup_temp_dir();
        let sui_content = r#"{- server -}
fn render(): String = "Hello, World!"

{@ render @}
<h1>{{ render() }}</h1>
"#;

        let source = create_simple_sui_file(&temp_dir, "app.sui", sui_content);
        let output_dir = temp_dir.path().join("public");

        let options = WebBuildOptions {
            output_dir: output_dir.clone(),
            module_name: "app".to_string(),
            optimize: false,
            minify_html: false,
        };

        let exit_code = web_build(&source, options);

        // Should succeed
        assert_eq!(exit_code, 0, "web_build should succeed");

        // Verify output files exist
        assert!(output_dir.join("app.html").exists(), "HTML file should exist");
        assert!(output_dir.join("app.manifest.json").exists(), "Manifest should exist");

        // Verify HTML content
        let html_content = fs::read_to_string(output_dir.join("app.html")).expect("Failed to read HTML");
        assert!(
            html_content.contains("<h1>"),
            "HTML should contain server-rendered content"
        );
    }

    #[test]
    fn test_web_build_with_client_code() {
        let temp_dir = setup_temp_dir();
        let sui_content = r#"{$ let count: i32 = 0 $}

{- server -}
fn render(): String = count.to_string()

{+ client +}
fn increment():
    count = count + 1

dom.getElementById("btn").addEventListener("click", increment)

{@ render @}
<div>Count: <span id="count">{{ count }}</span></div>
<button id="btn">Increment</button>
"#;

        let source = create_simple_sui_file(&temp_dir, "counter.sui", sui_content);
        let output_dir = temp_dir.path().join("public");

        let options = WebBuildOptions {
            output_dir: output_dir.clone(),
            module_name: "counter".to_string(),
            optimize: false,
            minify_html: false,
        };

        let exit_code = web_build(&source, options);

        assert_eq!(exit_code, 0, "web_build should succeed");

        // Verify WASM file exists
        assert!(output_dir.join("counter.wasm").exists(), "WASM file should exist");

        // Verify hydration script exists
        assert!(
            output_dir.join("counter.hydration.js").exists(),
            "Hydration script should exist"
        );

        // Verify HTML contains WASM loader
        let html_content = fs::read_to_string(output_dir.join("counter.html")).expect("Failed to read HTML");
        assert!(html_content.contains("loadWasm"), "HTML should contain WASM loader");
        assert!(html_content.contains("hydrate"), "HTML should contain hydration call");
    }

    #[test]
    fn test_web_build_optimization() {
        let temp_dir = setup_temp_dir();
        let sui_content = r#"{+ client +}
fn on_click():
    console.log("Clicked!")

{@ render @}
<button id="btn">Click Me</button>
"#;

        let source = create_simple_sui_file(&temp_dir, "app.sui", sui_content);
        let output_dir = temp_dir.path().join("dist");

        let options = WebBuildOptions {
            output_dir: output_dir.clone(),
            module_name: "app".to_string(),
            optimize: true,
            minify_html: true,
        };

        let exit_code = web_build(&source, options);

        assert_eq!(exit_code, 0, "web_build with optimization should succeed");

        // Verify files exist
        assert!(output_dir.join("app.html").exists());
        assert!(output_dir.join("app.wasm").exists());

        // Read HTML and verify minification
        let html_content = fs::read_to_string(output_dir.join("app.html")).expect("Failed to read HTML");

        // Minified HTML should have less whitespace
        let line_count = html_content.lines().count();
        assert!(
            line_count < 50,
            "Minified HTML should have fewer lines (got {})",
            line_count
        );

        // Note: WASM optimization requires wasm-opt to be installed
        // Test should pass even if wasm-opt is not available (graceful degradation)
    }

    #[test]
    fn test_web_build_multiple_event_bindings() {
        let temp_dir = setup_temp_dir();
        let sui_content = r#"{+ client +}
fn on_submit():
    console.log("Form submitted")

fn on_reset():
    console.log("Form reset")

dom.getElementById("form").addEventListener("submit", on_submit)
dom.getElementById("form").addEventListener("reset", on_reset)

{@ render @}
<form id="form">
    <input type="text" />
    <button type="submit">Submit</button>
    <button type="reset">Reset</button>
</form>
"#;

        let source = create_simple_sui_file(&temp_dir, "form.sui", sui_content);
        let output_dir = temp_dir.path().join("public");

        let options = WebBuildOptions {
            output_dir: output_dir.clone(),
            module_name: "form".to_string(),
            optimize: false,
            minify_html: false,
        };

        let exit_code = web_build(&source, options);

        assert_eq!(exit_code, 0, "web_build should succeed");

        // Read hydration script
        let hydration_script =
            fs::read_to_string(output_dir.join("form.hydration.js")).expect("Failed to read hydration script");

        // Verify both event bindings are present
        assert!(hydration_script.contains("submit"), "Should bind submit event");
        assert!(hydration_script.contains("reset"), "Should bind reset event");
        assert!(hydration_script.contains("on_submit"), "Should call on_submit handler");
        assert!(hydration_script.contains("on_reset"), "Should call on_reset handler");
    }

    #[test]
    fn test_web_init_creates_project() {
        let temp_dir = setup_temp_dir();
        let project_name = "my_web_app";

        // Change to temp directory
        let original_dir = std::env::current_dir().expect("Failed to get current dir");
        std::env::set_current_dir(temp_dir.path()).expect("Failed to change dir");

        let exit_code = web_init(project_name);

        // Restore original directory
        std::env::set_current_dir(original_dir).expect("Failed to restore dir");

        assert_eq!(exit_code, 0, "web_init should succeed");

        // Verify project structure
        let project_dir = temp_dir.path().join(project_name);
        assert!(project_dir.exists(), "Project directory should exist");
        assert!(project_dir.join("app.sui").exists(), "app.sui should exist");

        // Verify app.sui contains all required blocks
        let sui_content = fs::read_to_string(project_dir.join("app.sui")).expect("Failed to read app.sui");

        assert!(sui_content.contains("{$ "), "Should have shared state block");
        assert!(sui_content.contains("{- server -}"), "Should have server block");
        assert!(sui_content.contains("{+ client +}"), "Should have client block");
        assert!(sui_content.contains("{@ render @}"), "Should have template block");
    }

    #[test]
    fn test_web_build_error_handling_missing_file() {
        let temp_dir = setup_temp_dir();
        let non_existent = temp_dir.path().join("missing.sui");

        let options = WebBuildOptions {
            output_dir: temp_dir.path().join("public"),
            module_name: "app".to_string(),
            optimize: false,
            minify_html: false,
        };

        let exit_code = web_build(&non_existent, options);

        // Should fail gracefully
        assert_ne!(exit_code, 0, "web_build should fail for missing file");
    }

    #[test]
    fn test_web_build_error_handling_invalid_sui() {
        let temp_dir = setup_temp_dir();
        let invalid_sui = r#"This is not valid .sui syntax!
{- server -} with incomplete block
"#;

        let source = create_simple_sui_file(&temp_dir, "invalid.sui", invalid_sui);
        let output_dir = temp_dir.path().join("public");

        let options = WebBuildOptions {
            output_dir: output_dir.clone(),
            module_name: "app".to_string(),
            optimize: false,
            minify_html: false,
        };

        let exit_code = web_build(&source, options);

        // Should fail gracefully (parser error)
        assert_ne!(exit_code, 0, "web_build should fail for invalid syntax");
    }

    #[test]
    fn test_hydration_manifest_structure() {
        let temp_dir = setup_temp_dir();
        let sui_content = r#"{+ client +}
fn handler():
    console.log("Event fired")

dom.getElementById("btn").addEventListener("click", handler)

{@ render @}
<button id="btn">Click</button>
"#;

        let source = create_simple_sui_file(&temp_dir, "app.sui", sui_content);
        let output_dir = temp_dir.path().join("public");

        let options = WebBuildOptions {
            output_dir: output_dir.clone(),
            module_name: "app".to_string(),
            optimize: false,
            minify_html: false,
        };

        let exit_code = web_build(&source, options);
        assert_eq!(exit_code, 0);

        // Read and parse manifest JSON
        let manifest_path = output_dir.join("app.manifest.json");
        assert!(manifest_path.exists(), "Manifest should exist");

        let manifest_content = fs::read_to_string(manifest_path).expect("Failed to read manifest");

        // Verify manifest structure (basic JSON validation)
        assert!(manifest_content.contains("\"version\""), "Should have version field");
        assert!(manifest_content.contains("\"exports\""), "Should have exports field");
        assert!(manifest_content.contains("\"bindings\""), "Should have bindings field");

        // Verify specific binding
        assert!(
            manifest_content.contains("\"selector\""),
            "Should have selector in bindings"
        );
        assert!(manifest_content.contains("\"#btn\""), "Should bind to #btn");
        assert!(manifest_content.contains("\"click\""), "Should bind click event");
        assert!(manifest_content.contains("\"handler\""), "Should call handler function");
    }

    #[test]
    fn test_web_build_output_directory_creation() {
        let temp_dir = setup_temp_dir();
        let sui_content = r#"{@ render @}
<p>Test</p>
"#;

        let source = create_simple_sui_file(&temp_dir, "app.sui", sui_content);
        let output_dir = temp_dir.path().join("nested").join("output").join("dir");

        let options = WebBuildOptions {
            output_dir: output_dir.clone(),
            module_name: "app".to_string(),
            optimize: false,
            minify_html: false,
        };

        let exit_code = web_build(&source, options);

        assert_eq!(exit_code, 0, "web_build should create nested directories");
        assert!(output_dir.exists(), "Output directory should be created");
        assert!(
            output_dir.join("app.html").exists(),
            "Files should be created in nested directory"
        );
    }

    #[test]
    fn test_web_build_custom_module_name() {
        let temp_dir = setup_temp_dir();
        let sui_content = r#"{@ render @}
<p>Custom module name test</p>
"#;

        let source = create_simple_sui_file(&temp_dir, "app.sui", sui_content);
        let output_dir = temp_dir.path().join("public");

        let options = WebBuildOptions {
            output_dir: output_dir.clone(),
            module_name: "my_custom_app".to_string(),
            optimize: false,
            minify_html: false,
        };

        let exit_code = web_build(&source, options);

        assert_eq!(exit_code, 0);

        // Verify files have custom module name
        assert!(
            output_dir.join("my_custom_app.html").exists(),
            "HTML should use custom module name"
        );
        assert!(
            output_dir.join("my_custom_app.manifest.json").exists(),
            "Manifest should use custom module name"
        );

        // If there's client code, WASM should also use custom name
        // (This test has no client code, so no WASM file expected)
    }
}

#[cfg(test)]
mod web_integration_tests {
    use super::*;

    #[test]
    fn test_full_workflow_simple_app() {
        // This test simulates the full developer workflow:
        // 1. Create a .sui file
        // 2. Build it
        // 3. Verify all outputs
        // 4. Verify they can be served

        let temp_dir = setup_temp_dir();

        // Step 1: Create .sui file
        let sui_content = r#"{$ let message: String = "Hello from Simple!" $}

{- server -}
fn get_message(): String = message

{+ client +}
fn update_message():
    message = "Updated from client!"
    dom.getElementById("msg").textContent = message

dom.getElementById("btn").addEventListener("click", update_message)

{@ render @}
<!DOCTYPE html>
<html>
<head>
    <title>Simple Web App</title>
</head>
<body>
    <h1 id="msg">{{ get_message() }}</h1>
    <button id="btn">Update</button>
</body>
</html>
"#;

        let source = create_simple_sui_file(&temp_dir, "app.sui", sui_content);
        let output_dir = temp_dir.path().join("public");

        // Step 2: Build with optimization
        let options = WebBuildOptions {
            output_dir: output_dir.clone(),
            module_name: "app".to_string(),
            optimize: false, // Set to false to avoid wasm-opt dependency
            minify_html: true,
        };

        let exit_code = web_build(&source, options);
        assert_eq!(exit_code, 0, "Build should succeed");

        // Step 3: Verify all outputs
        let html_file = output_dir.join("app.html");
        let wasm_file = output_dir.join("app.wasm");
        let manifest_file = output_dir.join("app.manifest.json");
        let hydration_file = output_dir.join("app.hydration.js");

        assert!(html_file.exists(), "HTML file should exist");
        assert!(wasm_file.exists(), "WASM file should exist");
        assert!(manifest_file.exists(), "Manifest file should exist");
        assert!(hydration_file.exists(), "Hydration script should exist");

        // Step 4: Verify file contents
        let html_content = fs::read_to_string(html_file).expect("Failed to read HTML");
        let manifest_content = fs::read_to_string(manifest_file).expect("Failed to read manifest");
        let hydration_content = fs::read_to_string(hydration_file).expect("Failed to read hydration");

        // HTML should contain server-rendered message
        assert!(html_content.contains("Hello from Simple!"));

        // HTML should contain WASM loader
        assert!(html_content.contains("<script type=\"module\">"));
        assert!(html_content.contains("loadWasm"));

        // Manifest should have correct structure
        assert!(manifest_content.contains("\"version\": 2"));
        assert!(manifest_content.contains("\"#btn\""));
        assert!(manifest_content.contains("\"click\""));
        assert!(manifest_content.contains("\"update_message\""));

        // Hydration script should have correct binding
        assert!(hydration_content.contains("export async function hydrate"));
        assert!(hydration_content.contains("querySelector('#btn')"));
        assert!(hydration_content.contains("addEventListener('click'"));

        // Step 5: Verify file sizes are reasonable
        let wasm_size = fs::metadata(wasm_file).expect("Failed to get WASM metadata").len();
        assert!(wasm_size > 0, "WASM file should not be empty (got {} bytes)", wasm_size);
        assert!(
            wasm_size < 1024 * 1024,
            "WASM file should be < 1MB (got {} bytes)",
            wasm_size
        );
    }
}
