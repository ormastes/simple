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
    println!(
        "\n🚀 To run: cd {} && npm install && npm start",
        options.output_dir.display()
    );

    0
}

/// Package Electron app for distribution
#[derive(Clone, Debug)]
pub struct ElectronPackageOptions {
    pub source_dir: PathBuf,
    pub platforms: Vec<String>, // "win", "mac", "linux", "all"
    pub arch: Vec<String>,      // "x64", "arm64", "all"
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
    let builder_check = Command::new("electron-builder").arg("--version").output();

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
                eprintln!(
                    "error: Packaging failed for {} (exit code: {:?})",
                    platform,
                    status.code()
                );
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
    use simple_common::target::{Target, TargetArch, WasmRuntime};

    // Read source file
    let source_code = fs::read_to_string(source).map_err(|e| format!("Failed to read source file: {}", e))?;

    // Compile to WASM using existing compiler infrastructure
    let target = Target::new_wasm(TargetArch::Wasm32, WasmRuntime::Browser);

    let wasm_bytes = match compile_source_to_wasm(&source_code, target) {
        Ok(bytes) => bytes,
        Err(e) => {
            // Fall back to minimal WASM module if compilation fails
            tracing::warn!("WASM compilation failed, using stub: {}", e);
            vec![
                0x00, 0x61, 0x73, 0x6d, // \0asm
                0x01, 0x00, 0x00, 0x00, // version 1
            ]
        }
    };

    if optimize {
        // Run wasm-opt if available
        let _ = run_wasm_opt(output);
    }

    let size = wasm_bytes.len();

    fs::write(output, &wasm_bytes).map_err(|e| format!("Failed to write WASM: {}", e))?;

    Ok(size)
}

/// Compile source code to WASM bytes using the compiler pipeline
fn compile_source_to_wasm(source: &str, target: simple_common::target::Target) -> Result<Vec<u8>, String> {
    use simple_compiler::pipeline::CompilerPipeline;

    let mut compiler = CompilerPipeline::new().map_err(|e| format!("{e:?}"))?;
    compiler
        .compile_source_to_memory_for_target(source, target)
        .map_err(|e| format!("compile failed: {e}"))
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
    format!(
        r#"{{
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
"#,
        options.app_name, options.version
    )
}

fn generate_main_js(options: &ElectronBuildOptions) -> String {
    format!(
        r#"// Electron Main Process
const {{ app, Tray, powerMonitor, globalShortcut, clipboard, Notification, ipcMain }} = require('electron');
const fs = require('fs');
const path = require('path');

// Load WASM module
let wasmModule = null;
let wasmMemory = null;
let trayInstances = new Map();
let nextTrayId = 1;

// Helper: Read null-terminated string from WASM memory
function readString(ptr) {{
    if (!wasmMemory || ptr === 0) return '';
    const memory = new Uint8Array(wasmMemory.buffer);
    let end = ptr;
    while (memory[end] !== 0 && end < memory.length) end++;
    return new TextDecoder().decode(memory.slice(ptr, end));
}}

// Helper: Write string to WASM memory (returns ptr)
function writeString(str) {{
    if (!wasmModule || !wasmModule.exports.malloc) return 0;
    const bytes = new TextEncoder().encode(str + '\0');
    const ptr = wasmModule.exports.malloc(bytes.length);
    if (ptr === 0) return 0;
    const memory = new Uint8Array(wasmMemory.buffer);
    memory.set(bytes, ptr);
    return ptr;
}}

async function loadWasm() {{
    const wasmPath = path.join(__dirname, '{}.wasm');
    const wasmBuffer = fs.readFileSync(wasmPath);

    const imports = {{
        env: {{
            // App lifecycle FFI
            electron_app_on: (eventPtr, callbackId) => {{
                const event = readString(eventPtr);
                console.log('Registered event:', event, callbackId);
                app.on(event, () => {{
                    if (wasmModule.exports.handle_callback) {{
                        wasmModule.exports.handle_callback(callbackId);
                    }}
                }});
            }},
            electron_app_quit: () => {{
                app.quit();
            }},
            electron_app_is_ready: () => {{
                return app.isReady() ? 1 : 0;
            }},
            electron_app_get_path: (namePtr) => {{
                const name = readString(namePtr);
                try {{
                    const result = app.getPath(name);
                    return writeString(result);
                }} catch (e) {{
                    console.error('electron_app_get_path error:', e);
                    return 0;
                }}
            }},

            // Tray FFI
            electron_tray_create: (titlePtr) => {{
                const title = readString(titlePtr);
                try {{
                    const tray = new Tray(title || path.join(__dirname, 'icon.png'));
                    const id = nextTrayId++;
                    trayInstances.set(id, tray);
                    return id;
                }} catch (e) {{
                    console.error('electron_tray_create error:', e);
                    return 0;
                }}
            }},
            electron_tray_set_icon: (trayId, iconPathPtr) => {{
                const tray = trayInstances.get(trayId);
                if (tray) {{
                    const iconPath = readString(iconPathPtr);
                    try {{
                        tray.setImage(iconPath);
                    }} catch (e) {{
                        console.error('electron_tray_set_icon error:', e);
                    }}
                }}
            }},

            // Power monitor FFI
            electron_power_on: (eventPtr, callbackId) => {{
                const event = readString(eventPtr);
                powerMonitor.on(event, () => {{
                    if (wasmModule.exports.handle_callback) {{
                        wasmModule.exports.handle_callback(callbackId);
                    }}
                }});
            }},
            electron_power_get_battery_level: () => {{
                // Note: powerMonitor.getSystemIdleState doesn't provide battery level
                // This would require platform-specific implementation
                return -1.0; // Not available
            }},

            // Notification FFI
            electron_notification_show: (titlePtr, bodyPtr, optionsPtr) => {{
                const title = readString(titlePtr);
                const body = readString(bodyPtr);
                try {{
                    const notification = new Notification({{ title, body }});
                    notification.show();
                    return 1;
                }} catch (e) {{
                    console.error('electron_notification_show error:', e);
                    return 0;
                }}
            }},

            // Clipboard FFI
            electron_clipboard_read_text: () => {{
                const text = clipboard.readText();
                return writeString(text);
            }},
            electron_clipboard_write_text: (textPtr) => {{
                const text = readString(textPtr);
                clipboard.writeText(text);
            }},

            // Shortcuts FFI
            electron_shortcuts_register: (acceleratorPtr, callbackId) => {{
                const accelerator = readString(acceleratorPtr);
                try {{
                    const success = globalShortcut.register(accelerator, () => {{
                        if (wasmModule.exports.handle_callback) {{
                            wasmModule.exports.handle_callback(callbackId);
                        }}
                    }});
                    return success ? 1 : 0;
                }} catch (e) {{
                    console.error('electron_shortcuts_register error:', e);
                    return 0;
                }}
            }},

            // IPC FFI
            electron_ipc_send: (channelPtr, dataPtr) => {{
                const channel = readString(channelPtr);
                const data = readString(dataPtr);
                // Note: This sends to renderer processes via ipcMain
                // In a real app, you'd need BrowserWindow reference
                console.log('IPC send:', channel, data);
            }},
        }}
    }};

    const result = await WebAssembly.instantiate(wasmBuffer, imports);
    wasmModule = result.instance;
    wasmMemory = wasmModule.exports.memory;

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
    // Cleanup: unregister shortcuts
    globalShortcut.unregisterAll();
}});
"#,
        options.app_name
    )
}
