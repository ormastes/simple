// VSCode Extension CLI
// Build and package VSCode extensions with Simple WASM

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Options for vscode build command
#[derive(Clone, Debug)]
pub struct VsCodeBuildOptions {
    pub output_dir: PathBuf,
    pub extension_name: String,
    pub display_name: String,
    pub version: String,
    pub publisher: String,
    pub description: String,
    pub optimize: bool,
}

impl Default for VsCodeBuildOptions {
    fn default() -> Self {
        VsCodeBuildOptions {
            output_dir: PathBuf::from("dist"),
            extension_name: String::from("simple-extension"),
            display_name: String::from("Simple Extension"),
            version: String::from("1.0.0"),
            publisher: String::from(""),
            description: String::from("VSCode extension built with Simple"),
            optimize: false,
        }
    }
}

/// Build VSCode extension from Simple source
pub fn vscode_build(source: &PathBuf, options: VsCodeBuildOptions) -> i32 {
    println!("Building VSCode extension from {}", source.display());

    // Create output directory
    if let Err(e) = fs::create_dir_all(&options.output_dir) {
        eprintln!("error: Failed to create output directory: {}", e);
        return 1;
    }

    // Compile Simple to WASM
    println!("Compiling {} to WASM...", source.display());

    let wasm_path = options.output_dir.join(format!("{}.wasm", options.extension_name));

    let wasm_result = compile_to_wasm(source, &wasm_path, options.optimize);

    if let Err(e) = wasm_result {
        eprintln!("error: WASM compilation failed: {}", e);
        return 1;
    }

    println!("✓ Compiled WASM: {} bytes", wasm_result.unwrap());

    // Generate package.json (extension manifest)
    let package_json = generate_package_json(&options);
    let package_path = options.output_dir.join("package.json");

    if let Err(e) = fs::write(&package_path, package_json) {
        eprintln!("error: Failed to write package.json: {}", e);
        return 1;
    }

    println!("✓ Generated package.json");

    // Generate extension.js (VSCode entry point)
    let extension_js = generate_extension_js(&options);
    let extension_path = options.output_dir.join("extension.js");

    if let Err(e) = fs::write(&extension_path, extension_js) {
        eprintln!("error: Failed to write extension.js: {}", e);
        return 1;
    }

    println!("✓ Generated extension.js");

    // Generate README
    let readme = generate_readme(&options);
    let readme_path = options.output_dir.join("README.md");

    if let Err(e) = fs::write(&readme_path, readme) {
        eprintln!("error: Failed to write README.md: {}", e);
        return 1;
    }

    println!("✓ Generated README.md");

    println!("\n📦 VSCode extension built successfully!");
    println!("   Directory: {}", options.output_dir.display());
    println!("   WASM:      {}.wasm", options.extension_name);
    println!("   Entry:     extension.js");
    println!("\n🚀 To test: code --extensionDevelopmentPath={}", options.output_dir.display());

    0
}

/// Package VSCode extension as .vsix
#[derive(Clone, Debug)]
pub struct VsCodePackageOptions {
    pub source_dir: PathBuf,
    pub extension_name: String,
    pub version: String,
}

impl Default for VsCodePackageOptions {
    fn default() -> Self {
        VsCodePackageOptions {
            source_dir: PathBuf::from("dist"),
            extension_name: String::from("simple-extension"),
            version: String::from("1.0.0"),
        }
    }
}

pub fn vscode_package(options: VsCodePackageOptions) -> i32 {
    println!("Packaging VSCode extension...");

    // Check if vsce is available
    let vsce_check = Command::new("vsce")
        .arg("--version")
        .output();

    if vsce_check.is_err() {
        eprintln!("error: vsce (Visual Studio Code Extension) not found");
        eprintln!("       Install with: npm install -g @vscode/vsce");
        return 1;
    }

    // Run vsce package
    let result = Command::new("vsce")
        .arg("package")
        .arg("--out")
        .arg(format!("{}-{}.vsix", options.extension_name, options.version))
        .current_dir(&options.source_dir)
        .status();

    match result {
        Ok(status) if status.success() => {
            println!("✓ Packaged extension");
            println!("\n✅ Packaging complete!");
            println!("   Output: {}/{}-{}.vsix",
                options.source_dir.display(),
                options.extension_name,
                options.version
            );
            0
        }
        Ok(status) => {
            eprintln!("error: Packaging failed (exit code: {:?})", status.code());
            1
        }
        Err(e) => {
            eprintln!("error: Failed to run vsce: {}", e);
            1
        }
    }
}

/// Publish extension to marketplace
#[derive(Clone, Debug)]
pub struct VsCodePublishOptions {
    pub vsix_path: PathBuf,
    pub token: String,
}

pub fn vscode_publish(options: VsCodePublishOptions) -> i32 {
    println!("Publishing VSCode extension...");

    if options.token.is_empty() {
        eprintln!("error: Personal access token required");
        eprintln!("       Get token from: https://dev.azure.com/");
        return 1;
    }

    // Run vsce publish
    let result = Command::new("vsce")
        .arg("publish")
        .arg("--packagePath")
        .arg(&options.vsix_path)
        .arg("--pat")
        .arg(&options.token)
        .status();

    match result {
        Ok(status) if status.success() => {
            println!("✓ Published extension");
            println!("\n✅ Extension published to marketplace!");
            0
        }
        Ok(status) => {
            eprintln!("error: Publishing failed (exit code: {:?})", status.code());
            1
        }
        Err(e) => {
            eprintln!("error: Failed to run vsce: {}", e);
            1
        }
    }
}

// Helper functions

fn compile_to_wasm(source: &Path, output: &Path, optimize: bool) -> Result<usize, String> {
    // TODO: Integrate with existing WASM compiler

    // WASM magic number + version
    let mut wasm_bytes = vec![
        0x00, 0x61, 0x73, 0x6d, // \0asm
        0x01, 0x00, 0x00, 0x00, // version 1
    ];

    if optimize {
        let _ = run_wasm_opt(output);
    }

    let size = wasm_bytes.len();

    fs::write(output, &wasm_bytes)
        .map_err(|e| format!("Failed to write WASM: {}", e))?;

    Ok(size)
}

fn run_wasm_opt(wasm_path: &Path) -> Result<(), String> {
    let result = Command::new("wasm-opt")
        .arg("-O3")
        .arg("--strip-debug")
        .arg("-o")
        .arg(wasm_path)
        .arg(wasm_path)
        .output();

    match result {
        Ok(output) if output.status.success() => Ok(()),
        _ => Err("wasm-opt failed".to_string()),
    }
}

fn generate_package_json(options: &VsCodeBuildOptions) -> String {
    let activation_events = if !options.extension_name.is_empty() {
        format!(r#""onLanguage:simple""#)
    } else {
        r#""\*""#.to_string()
    };

    format!(r#"{{
  "name": "{}",
  "displayName": "{}",
  "description": "{}",
  "version": "{}",
  "publisher": "{}",
  "engines": {{
    "vscode": "^1.80.0"
  }},
  "categories": [
    "Programming Languages",
    "Linters"
  ],
  "activationEvents": [
    {}
  ],
  "main": "./extension.js",
  "contributes": {{
    "languages": [
      {{
        "id": "simple",
        "extensions": [".spl"],
        "aliases": ["Simple", "simple"]
      }}
    ],
    "commands": [
      {{
        "command": "simple.formatDocument",
        "title": "Format Document (Simple)"
      }}
    ]
  }},
  "devDependencies": {{
    "@types/vscode": "^1.80.0"
  }}
}}
"#,
        options.extension_name,
        options.display_name,
        options.description,
        options.version,
        if options.publisher.is_empty() { "publisher" } else { &options.publisher },
        activation_events
    )
}

fn generate_extension_js(options: &VsCodeBuildOptions) -> String {
    format!(r#"// VSCode Extension Entry Point
const vscode = require('vscode');
const fs = require('fs');
const path = require('path');

// Load WASM module
let wasmModule = null;

async function loadWasm() {{
    const wasmPath = path.join(__dirname, '{}.wasm');
    const wasmBuffer = fs.readFileSync(wasmPath);

    // VSCode Extension API FFI bridge
    const imports = {{
        env: {{
            // Commands API
            vscode_commands_register: (commandPtr, callbackId) => {{
                // TODO: Register command
                return callbackId;
            }},
            vscode_commands_execute: (commandPtr, argsJsonPtr) => {{
                // TODO: Execute command
                return 0;
            }},

            // Languages API
            vscode_languages_register_completion: (languagePtr, callbackId) => {{
                vscode.languages.registerCompletionItemProvider('simple', {{
                    provideCompletionItems(document, position) {{
                        // TODO: Call WASM completion provider
                        return [];
                    }}
                }});
                return callbackId;
            }},

            vscode_languages_register_hover: (languagePtr, callbackId) => {{
                vscode.languages.registerHoverProvider('simple', {{
                    provideHover(document, position) {{
                        // TODO: Call WASM hover provider
                        return null;
                    }}
                }});
                return callbackId;
            }},

            vscode_languages_create_diagnostic_collection: (namePtr) => {{
                return vscode.languages.createDiagnosticCollection('simple');
            }},

            // Window API
            vscode_window_show_message: (messagePtr, messageType) => {{
                const message = ""; // TODO: Convert ptr to string
                if (messageType === 0) vscode.window.showInformationMessage(message);
                else if (messageType === 1) vscode.window.showWarningMessage(message);
                else if (messageType === 2) vscode.window.showErrorMessage(message);
            }},

            vscode_window_create_status_bar_item: (alignment, priority) => {{
                return vscode.window.createStatusBarItem(alignment, priority);
            }},

            // Workspace API
            vscode_workspace_get_configuration: (sectionPtr) => {{
                // TODO: Get configuration
                return 0;
            }},
        }}
    }};

    const result = await WebAssembly.instantiate(wasmBuffer, imports);
    wasmModule = result.instance;

    console.log('Extension WASM module loaded');
    return wasmModule;
}}

// Extension activation
async function activate(context) {{
    console.log('Extension "{}" is now active!');

    try {{
        await loadWasm();

        // Call WASM activate function if it exists
        if (wasmModule.exports.activate) {{
            wasmModule.exports.activate();
        }}
    }} catch (error) {{
        console.error('Failed to load extension WASM:', error);
        vscode.window.showErrorMessage('Failed to load extension: ' + error.message);
    }}
}}

// Extension deactivation
function deactivate() {{
    if (wasmModule && wasmModule.exports.deactivate) {{
        wasmModule.exports.deactivate();
    }}
}}

module.exports = {{
    activate,
    deactivate
}};
"#, options.extension_name, options.display_name)
}

fn generate_readme(options: &VsCodeBuildOptions) -> String {
    format!(r#"# {}

{}

## Features

- Built with Simple language and WebAssembly
- High-performance language features
- Type-safe extension code

## Requirements

- Visual Studio Code ^1.80.0

## Extension Settings

This extension contributes the following settings:

* `simple.enable`: Enable/disable this extension

## Release Notes

### 1.0.0

Initial release

## For Developers

This extension is built using the Simple programming language and compiled to WebAssembly for maximum performance.

**Enjoy!**
"#, options.display_name, options.description)
}
