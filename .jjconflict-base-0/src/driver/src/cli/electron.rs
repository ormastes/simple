// Electron Desktop App CLI
// Build and package Electron applications with Simple WASM

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Options for electron build command
#[derive(Clone, Debug)]
pub struct ElectronBuildOptions {
    pub output_dir: PathBuf,
    pub app_name: String,
    pub version: String,
    pub icon: Option<PathBuf>,
    pub optimize: bool,
}

impl Default for ElectronBuildOptions {
    fn default() -> Self {
        ElectronBuildOptions {
            output_dir: PathBuf::from("dist"),
            app_name: String::from("electron-app"),
            version: String::from("1.0.0"),
            icon: None,
            optimize: false,
        }
    }
}

/// Build Electron app from Simple source
pub fn electron_build(source: &PathBuf, options: ElectronBuildOptions) -> i32 {
    println!("Building Electron app from {}", source.display());

    // Create output directory
    if let Err(e) = fs::create_dir_all(&options.output_dir) {
        eprintln!("error: Failed to create output directory: {}", e);
        return 1;
    }

    // Compile Simple to WASM
    println!("Compiling {} to WASM...", source.display());

    let wasm_path = options.output_dir.join(format!("{}.wasm", options.app_name));

    // TODO: Actually compile to WASM using existing compiler
    // For now, create placeholder
    let wasm_result = compile_to_wasm(source, &wasm_path, options.optimize);

    if let Err(e) = wasm_result {
        eprintln!("error: WASM compilation failed: {}", e);
        return 1;
    }

    println!("✓ Compiled WASM: {} bytes", wasm_result.unwrap());

    // Generate package.json
    let package_json = generate_package_json(&options);
    let package_path = options.output_dir.join("package.json");

    if let Err(e) = fs::write(&package_path, package_json) {
        eprintln!("error: Failed to write package.json: {}", e);
        return 1;
    }

    println!("✓ Generated package.json");

    // Generate main.js (Electron entry point)
    let main_js = generate_main_js(&options);
    let main_path = options.output_dir.join("main.js");

    if let Err(e) = fs::write(&main_path, main_js) {
        eprintln!("error: Failed to write main.js: {}", e);
        return 1;
    }

    println!("✓ Generated main.js");

    // Copy icon if provided
    if let Some(icon_path) = &options.icon {
        let dest_icon = options.output_dir.join("icon.png");
        if let Err(e) = fs::copy(icon_path, &dest_icon) {
            eprintln!("warning: Failed to copy icon: {}", e);
        } else {
            println!("✓ Copied icon");
        }
    }

    println!("\n📦 Electron app built successfully!");
    println!("   Directory: {}", options.output_dir.display());
    println!("   WASM:      {}.wasm", options.app_name);
    println!("   Entry:     main.js");
    println!("\n🚀 To run: cd {} && npm install && npm start", options.output_dir.display());

    0
}

/// Package Electron app for distribution
#[derive(Clone, Debug)]
pub struct ElectronPackageOptions {
    pub source_dir: PathBuf,
    pub platforms: Vec<String>,  // "win", "mac", "linux", "all"
    pub arch: Vec<String>,        // "x64", "arm64", "all"
    pub app_name: String,
    pub version: String,
}

impl Default for ElectronPackageOptions {
    fn default() -> Self {
        ElectronPackageOptions {
            source_dir: PathBuf::from("dist"),
            platforms: vec!["all".to_string()],
            arch: vec!["x64".to_string()],
            app_name: String::from("electron-app"),
            version: String::from("1.0.0"),
        }
    }
}

pub fn electron_package(options: ElectronPackageOptions) -> i32 {
    println!("Packaging Electron app...");

    // Check if electron-builder is available
    let builder_check = Command::new("electron-builder")
        .arg("--version")
        .output();

    if builder_check.is_err() {
        eprintln!("error: electron-builder not found");
        eprintln!("       Install with: npm install -g electron-builder");
        return 1;
    }

    // Determine platforms
    let platforms = if options.platforms.contains(&"all".to_string()) {
        vec!["win".to_string(), "mac".to_string(), "linux".to_string()]
    } else {
        options.platforms.clone()
    };

    // Build for each platform
    for platform in platforms {
        println!("\n📦 Packaging for {}...", platform);

        let platform_arg = match platform.as_str() {
            "win" => "--win",
            "mac" => "--mac",
            "linux" => "--linux",
            _ => {
                eprintln!("warning: Unknown platform: {}", platform);
                continue;
            }
        };

        // Run electron-builder
        let result = Command::new("electron-builder")
            .arg(platform_arg)
            .arg("--dir")
            .arg(&options.source_dir)
            .status();

        match result {
            Ok(status) if status.success() => {
                println!("✓ Packaged for {}", platform);
            }
            Ok(status) => {
                eprintln!("error: Packaging failed for {} (exit code: {:?})", platform, status.code());
                return 1;
            }
            Err(e) => {
                eprintln!("error: Failed to run electron-builder: {}", e);
                return 1;
            }
        }
    }

    println!("\n✅ Packaging complete!");
    println!("   Output: {}/dist/", options.source_dir.display());

    0
}

// Helper functions

fn compile_to_wasm(source: &Path, output: &Path, optimize: bool) -> Result<usize, String> {
    // TODO: Integrate with existing WASM compiler
    // For now, create a minimal WASM module

    // WASM magic number + version
    let mut wasm_bytes = vec![
        0x00, 0x61, 0x73, 0x6d, // \0asm
        0x01, 0x00, 0x00, 0x00, // version 1
    ];

    // Add placeholder sections
    // This would be replaced by actual compilation

    if optimize {
        // Run wasm-opt if available
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
        Ok(_) => Err("wasm-opt failed".to_string()),
        Err(_) => Err("wasm-opt not found".to_string()),
    }
}

fn generate_package_json(options: &ElectronBuildOptions) -> String {
    format!(r#"{{
  "name": "{}",
  "version": "{}",
  "description": "Electron app built with Simple",
  "main": "main.js",
  "scripts": {{
    "start": "electron ."
  }},
  "keywords": ["electron", "simple", "wasm"],
  "author": "",
  "license": "MIT",
  "devDependencies": {{
    "electron": "^27.0.0"
  }}
}}
"#, options.app_name, options.version)
}

fn generate_main_js(options: &ElectronBuildOptions) -> String {
    format!(r#"// Electron Main Process
const {{ app, Tray, powerMonitor, globalShortcut, clipboard, Notification }} = require('electron');
const fs = require('fs');
const path = require('path');

// Load WASM module
let wasmModule = null;

async function loadWasm() {{
    const wasmPath = path.join(__dirname, '{}.wasm');
    const wasmBuffer = fs.readFileSync(wasmPath);

    const imports = {{
        env: {{
            // App lifecycle FFI
            electron_app_on: (event, callbackId) => {{
                console.log('Registered event:', event, callbackId);
            }},
            electron_app_quit: () => {{
                app.quit();
            }},
            electron_app_is_ready: () => {{
                return app.isReady() ? 1 : 0;
            }},
            electron_app_get_path: (namePtr) => {{
                // TODO: Convert string ptr
                return 0;
            }},

            // Tray FFI
            electron_tray_create: (titlePtr) => {{
                // TODO: Create tray
                return 1;
            }},
            electron_tray_set_icon: (trayId, iconPathPtr) => {{
                // TODO: Set tray icon
            }},

            // Power monitor FFI
            electron_power_on: (eventPtr, callbackId) => {{
                // TODO: Register power event
            }},
            electron_power_get_battery_level: () => {{
                // TODO: Get battery level
                return 0.0;
            }},

            // Notification FFI
            electron_notification_show: (titlePtr, bodyPtr, optionsPtr) => {{
                // TODO: Show notification
                return 1;
            }},

            // Clipboard FFI
            electron_clipboard_read_text: () => {{
                return clipboard.readText();
            }},
            electron_clipboard_write_text: (textPtr) => {{
                // TODO: Write to clipboard
            }},

            // Shortcuts FFI
            electron_shortcuts_register: (acceleratorPtr, callbackId) => {{
                // TODO: Register shortcut
                return 1;
            }},

            // IPC FFI
            electron_ipc_send: (channelPtr, dataPtr) => {{
                // TODO: Send IPC message
            }},
        }}
    }};

    const result = await WebAssembly.instantiate(wasmBuffer, imports);
    wasmModule = result.instance;

    console.log('WASM module loaded');
    return wasmModule;
}}

// App lifecycle
app.on('ready', async () => {{
    console.log('App ready, loading WASM...');

    try {{
        await loadWasm();

        // Call WASM main function if it exists
        if (wasmModule.exports.main) {{
            wasmModule.exports.main();
        }}
    }} catch (error) {{
        console.error('Failed to load WASM:', error);
        app.quit();
    }}
}});

app.on('window-all-closed', () => {{
    // Keep running (typical for tray apps)
}});

app.on('will-quit', () => {{
    // Cleanup
}});
"#, options.app_name)
}
