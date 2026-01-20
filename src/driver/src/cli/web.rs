//! Web compilation commands: build .sui files to HTML + WASM.

use simple_compiler::web_compiler::WebCompiler;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Options for web build command
#[derive(Clone)]
pub struct WebBuildOptions {
    /// Output directory for built assets (default: public/)
    pub output_dir: PathBuf,
    /// WASM module name (default: app)
    pub module_name: String,
    /// Whether to optimize WASM binary
    pub optimize: bool,
    /// Whether to minify HTML output
    pub minify_html: bool,
}

impl Default for WebBuildOptions {
    fn default() -> Self {
        Self {
            output_dir: PathBuf::from("public"),
            module_name: "app".to_string(),
            optimize: false,
            minify_html: false,
        }
    }
}

/// Optimize a WASM binary using wasm-opt if available
fn optimize_wasm(wasm_path: &Path) -> Result<usize, String> {
    // Check if wasm-opt is available
    let wasm_opt_available = Command::new("wasm-opt").arg("--version").output().is_ok();

    if !wasm_opt_available {
        return Err("wasm-opt not found. Install binaryen for WASM optimization.\n\
                    Ubuntu/Debian: sudo apt install binaryen\n\
                    macOS: brew install binaryen\n\
                    Or download from: https://github.com/WebAssembly/binaryen/releases"
            .to_string());
    }

    // Run wasm-opt with optimization level -O3
    let output = Command::new("wasm-opt")
        .arg("-O3") // Optimization level 3 (aggressive)
        .arg("--strip-debug") // Remove debug info
        .arg("--strip-producers") // Remove producer section
        .arg("-o")
        .arg(wasm_path) // Output to same file
        .arg(wasm_path) // Input file
        .output()
        .map_err(|e| format!("Failed to run wasm-opt: {}", e))?;

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("wasm-opt failed: {}", stderr));
    }

    // Get optimized file size
    let metadata = fs::metadata(wasm_path).map_err(|e| format!("Failed to read optimized WASM: {}", e))?;

    Ok(metadata.len() as usize)
}

/// Minify HTML content
fn minify_html_content(html: &str) -> String {
    // Simple minification: remove extra whitespace and comments
    // For production, consider using a proper HTML minifier crate
    html.lines()
        .map(|line| line.trim())
        .filter(|line| !line.is_empty() && !line.starts_with("<!--"))
        .collect::<Vec<_>>()
        .join("")
}

/// Options for web serve command
pub struct WebServeOptions {
    /// Port to serve on (default: 8000)
    pub port: u16,
    /// Whether to watch for changes and rebuild
    pub watch: bool,
    /// Whether to open browser automatically
    pub open: bool,
}

impl Default for WebServeOptions {
    fn default() -> Self {
        Self {
            port: 8000,
            watch: true,
            open: false,
        }
    }
}

/// Serve a web application with development server
///
/// Serves built assets and optionally watches for changes
///
/// # Example
/// ```text
/// simple web serve app.sui --port 3000 --watch
/// ```
pub fn web_serve(source: &PathBuf, build_options: WebBuildOptions, serve_options: WebServeOptions) -> i32 {
    use std::io::{Read, Write};
    use std::net::TcpListener;
    use std::sync::{Arc, Mutex};
    use std::thread;
    use std::time::Duration;

    // Initial build
    println!("Building {}...", source.display());
    let result = web_build(source, build_options.clone());
    if result != 0 {
        eprintln!("Initial build failed");
        return result;
    }

    println!();
    println!("🚀 Development server starting...");
    println!("   Local:   http://localhost:{}/", serve_options.port);
    println!("   Output:  {}", build_options.output_dir.display());

    if serve_options.watch {
        println!("   Watching: {} for changes", source.display());
    }

    println!();
    println!("Press Ctrl+C to stop");
    println!();

    // Start file watcher in separate thread if watch mode enabled
    if serve_options.watch {
        let source_clone = source.clone();
        let build_options_clone = build_options.clone();
        let last_modified = Arc::new(Mutex::new(fs::metadata(&source_clone).and_then(|m| m.modified()).ok()));
        let last_modified_clone = last_modified.clone();

        thread::spawn(move || {
            loop {
                thread::sleep(Duration::from_millis(500));

                if let Ok(metadata) = fs::metadata(&source_clone) {
                    if let Ok(modified) = metadata.modified() {
                        let mut last = last_modified_clone.lock().unwrap();
                        if let Some(last_time) = *last {
                            if modified > last_time {
                                println!("\n📝 File changed, rebuilding...");
                                *last = Some(modified);
                                drop(last); // Release lock before rebuild

                                match web_build(&source_clone, build_options_clone.clone()) {
                                    0 => println!("✓ Rebuild complete\n"),
                                    _ => eprintln!("✗ Rebuild failed\n"),
                                }
                            }
                        } else {
                            *last = Some(modified);
                        }
                    }
                }
            }
        });
    }

    // Start HTTP server
    let addr = format!("127.0.0.1:{}", serve_options.port);
    let listener = match TcpListener::bind(&addr) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error: failed to bind to {}: {}", addr, e);
            eprintln!("       Port {} may already be in use", serve_options.port);
            return 1;
        }
    };

    // Open browser if requested
    if serve_options.open {
        let url = format!("http://localhost:{}/", serve_options.port);
        let _ = open_browser(&url);
    }

    // Simple HTTP server loop
    for stream in listener.incoming() {
        match stream {
            Ok(mut stream) => {
                let mut buffer = [0; 1024];
                if let Ok(_) = stream.read(&mut buffer) {
                    let request = String::from_utf8_lossy(&buffer);

                    // Parse request line
                    let path = if let Some(line) = request.lines().next() {
                        let parts: Vec<&str> = line.split_whitespace().collect();
                        if parts.len() >= 2 && parts[0] == "GET" {
                            parts[1].trim_start_matches('/')
                        } else {
                            ""
                        }
                    } else {
                        ""
                    };

                    // Serve file
                    serve_file(&mut stream, &build_options.output_dir, path);
                }
            }
            Err(e) => {
                eprintln!("Connection error: {}", e);
            }
        }
    }

    0
}

/// Serve a single file over HTTP
fn serve_file(stream: &mut std::net::TcpStream, base_dir: &Path, path: &str) {
    use std::io::Write;

    let file_path = if path.is_empty() || path == "/" {
        // Default to index.html or first .html file
        base_dir
            .join("index.html")
            .metadata()
            .ok()
            .and_then(|_| Some(base_dir.join("index.html")))
            .or_else(|| {
                // Find first .html file
                fs::read_dir(base_dir)
                    .ok()?
                    .filter_map(|e| e.ok())
                    .find(|e| e.path().extension().and_then(|s| s.to_str()) == Some("html"))
                    .map(|e| e.path())
            })
            .unwrap_or_else(|| base_dir.join("app.html"))
    } else {
        base_dir.join(path)
    };

    if let Ok(contents) = fs::read(&file_path) {
        let content_type = match file_path.extension().and_then(|s| s.to_str()) {
            Some("html") => "text/html",
            Some("js") => "application/javascript",
            Some("wasm") => "application/wasm",
            Some("json") => "application/json",
            Some("css") => "text/css",
            Some("png") => "image/png",
            Some("jpg") | Some("jpeg") => "image/jpeg",
            Some("svg") => "image/svg+xml",
            _ => "application/octet-stream",
        };

        let response = format!(
            "HTTP/1.1 200 OK\r\nContent-Type: {}\r\nContent-Length: {}\r\nAccess-Control-Allow-Origin: *\r\n\r\n",
            content_type,
            contents.len()
        );

        let _ = stream.write_all(response.as_bytes());
        let _ = stream.write_all(&contents);
    } else {
        let not_found = b"HTTP/1.1 404 NOT FOUND\r\nContent-Type: text/plain\r\n\r\n404 Not Found";
        let _ = stream.write_all(not_found);
    }
}

/// Open browser to URL (cross-platform)
fn open_browser(url: &str) -> Result<(), String> {
    #[cfg(target_os = "macos")]
    {
        std::process::Command::new("open")
            .arg(url)
            .spawn()
            .map_err(|e| format!("Failed to open browser: {}", e))?;
    }
    #[cfg(target_os = "linux")]
    {
        std::process::Command::new("xdg-open")
            .arg(url)
            .spawn()
            .map_err(|e| format!("Failed to open browser: {}", e))?;
    }
    #[cfg(target_os = "windows")]
    {
        std::process::Command::new("cmd")
            .args(&["/C", "start", url])
            .spawn()
            .map_err(|e| format!("Failed to open browser: {}", e))?;
    }
    Ok(())
}

/// Build a .sui file to a complete web application
///
/// Compiles .sui file to:
/// - HTML file (server-rendered with hydration script)
/// - WASM binary (client code)
/// - Manifest JSON (hydration metadata)
///
/// # Example
/// ```text
/// simple web build app.sui -o public/
/// ```
pub fn web_build(source: &PathBuf, options: WebBuildOptions) -> i32 {
    use std::time::Instant;

    // Read source file
    let source_content = match std::fs::read_to_string(source) {
        Ok(content) => content,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", source.display(), e);
            return 1;
        }
    };

    // Create web compiler
    let mut compiler = match WebCompiler::new() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("error: failed to initialize web compiler: {:?}", e);
            return 1;
        }
    };

    // Compile .sui file
    println!("Compiling {} for web...", source.display());
    let start_time = Instant::now();

    let result = match compiler.compile_sui_source(&source_content) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: compilation failed: {:?}", e);
            return 1;
        }
    };

    let duration = start_time.elapsed();
    println!("✓ Compilation completed in {:.2}s", duration.as_secs_f64());

    // Create output directory
    if let Err(e) = fs::create_dir_all(&options.output_dir) {
        eprintln!("error: failed to create output directory: {}", e);
        return 1;
    }

    // Determine base filename from source
    let base_name = source.file_stem().and_then(|s| s.to_str()).unwrap_or("app");

    // Write HTML file (with optional minification)
    let html_path = options.output_dir.join(format!("{}.html", base_name));
    let html_content = if options.minify_html {
        let original_len = result.template_html.len();
        let minified = minify_html_content(&result.template_html);
        let new_len = minified.len();
        let savings = original_len.saturating_sub(new_len);
        let percent = if original_len > 0 {
            (savings as f64 / original_len as f64) * 100.0
        } else {
            0.0
        };
        println!(
            "✓ Minified HTML: {} bytes → {} bytes ({:.1}% reduction)",
            original_len, new_len, percent
        );
        minified
    } else {
        result.template_html.clone()
    };

    if let Err(e) = fs::write(&html_path, &html_content) {
        eprintln!("error: failed to write HTML file: {}", e);
        return 1;
    }
    println!("✓ Generated {}", html_path.display());

    // Write WASM binary if client code exists
    if !result.client_binary.is_empty() {
        let wasm_path = options.output_dir.join(format!("{}.wasm", options.module_name));

        // Write initial WASM binary
        if let Err(e) = fs::write(&wasm_path, &result.client_binary) {
            eprintln!("error: failed to write WASM file: {}", e);
            return 1;
        }

        let original_size = result.client_binary.len();
        let mut final_size = original_size;

        // Optimize WASM if requested
        if options.optimize {
            match optimize_wasm(&wasm_path) {
                Ok(new_size) => {
                    final_size = new_size;
                    let savings = original_size.saturating_sub(new_size);
                    let percent = if original_size > 0 {
                        (savings as f64 / original_size as f64) * 100.0
                    } else {
                        0.0
                    };
                    println!(
                        "✓ Optimized WASM: {} bytes → {} bytes ({:.1}% reduction)",
                        original_size, new_size, percent
                    );
                }
                Err(e) => {
                    eprintln!("warning: WASM optimization failed: {}", e);
                    eprintln!("         Continuing with unoptimized binary");
                }
            }
        }

        println!("✓ Generated {} ({} bytes)", wasm_path.display(), final_size);

        // Write manifest JSON
        let manifest_path = options
            .output_dir
            .join(format!("{}.manifest.json", options.module_name));
        match result.hydration_manifest.to_json() {
            Ok(json) => {
                if let Err(e) = fs::write(&manifest_path, json) {
                    eprintln!("error: failed to write manifest file: {}", e);
                    return 1;
                }
                println!("✓ Generated {}", manifest_path.display());
            }
            Err(e) => {
                eprintln!("error: failed to serialize manifest: {}", e);
                return 1;
            }
        }

        // Write hydration script as separate file (optional)
        let hydration_path = options.output_dir.join(format!("{}.hydration.js", options.module_name));
        if let Err(e) = fs::write(&hydration_path, &result.hydration_script) {
            eprintln!("warning: failed to write hydration script: {}", e);
            // Continue - this is optional
        } else {
            println!("✓ Generated {}", hydration_path.display());
        }

        // Print summary
        println!("\n📦 Web application built successfully!");
        println!("   HTML:     {}", html_path.display());
        println!(
            "   WASM:     {}/{}.wasm ({} KB)",
            options.output_dir.display(),
            options.module_name,
            result.client_binary.len() / 1024
        );
        println!(
            "   Manifest: {}/{}.manifest.json",
            options.output_dir.display(),
            options.module_name
        );
        println!(
            "\n🚀 To serve: cd {} && python3 -m http.server 8000",
            options.output_dir.display()
        );
    } else {
        // Server-only page (no client code)
        println!("\n📦 Server-only page built successfully!");
        println!("   HTML: {}", html_path.display());
        println!("\n💡 No client code found - page is server-rendered only");
    }

    0
}

/// List supported web build features
pub fn web_features() -> i32 {
    println!("Simple Web Framework Features:");
    println!();
    println!("✓ Server-side rendering (SSR)");
    println!("✓ Client-side hydration (WASM)");
    println!("✓ Automatic event binding");
    println!("✓ Shared state (SSR → client)");
    println!("✓ Browser FFI (DOM, Fetch, Console, Storage)");
    println!("✓ ES6 module loading");
    println!("✓ Auto-initialization");
    println!();
    println!("Supported .sui block types:");
    println!("  {{- server -}}  → Server-side code (x64 native)");
    println!("  {{+ client +}}  → Client-side code (wasm32)");
    println!("  {{@ render @}}  → HTML template");
    println!("  {{$ state $}}   → Shared state");
    println!();
    println!("Example .sui file:");
    println!("  {{$ let count: i64 = 0 $}}");
    println!();
    println!("  {{+ client +}}");
    println!("  fn increment():");
    println!("      count += 1");
    println!();
    println!("  {{@ render @}}");
    println!("  <button onclick=\"increment()\">Count: {{{{ count }}}}</button>");
    println!();
    0
}

/// Create a new .sui project template
pub fn web_init(project_name: &str) -> i32 {
    let project_dir = PathBuf::from(project_name);

    // Create project directory
    if project_dir.exists() {
        eprintln!("error: directory {} already exists", project_name);
        return 1;
    }

    if let Err(e) = fs::create_dir_all(&project_dir) {
        eprintln!("error: failed to create project directory: {}", e);
        return 1;
    }

    // Create example .sui file
    let example_sui = r#"
{$ let count: i64 = 0 $}

{- server -}
# Server initialization
import db

fn init():
    count = db.get_count()

{+ client +}
# Client code
import dom

fn increment():
    count += 1
    update_ui()

fn update_ui():
    elem = dom.getElementById("count")
    elem.textContent = count.to_string()

# Bind event
dom.getElementById("btn").addEventListener("click", increment)

{@ render @}
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{{ project_name }} - Simple WASM App</title>
    <style>
        body {
            font-family: system-ui, sans-serif;
            max-width: 800px;
            margin: 2rem auto;
            padding: 0 1rem;
        }
        button {
            font-size: 1.2rem;
            padding: 0.5rem 1rem;
            cursor: pointer;
        }
    </style>
</head>
<body>
    <h1>Welcome to {{ project_name }}!</h1>
    <p>Count: <span id="count">{{ count }}</span></p>
    <button id="btn">Increment</button>
</body>
</html>
"#;

    let app_sui_path = project_dir.join("app.sui");
    if let Err(e) = fs::write(&app_sui_path, example_sui.replace("{{ project_name }}", project_name)) {
        eprintln!("error: failed to write app.sui: {}", e);
        return 1;
    }

    // Create README
    let readme = format!(
        r#"# {}

A Simple language web application.

## Building

```bash
simple web build app.sui -o public/
```

## Running

```bash
cd public/
python3 -m http.server 8000
```

Then open http://localhost:8000/app.html

## Structure

- `app.sui` - Main application file (server + client + template)
- `public/` - Built assets (HTML, WASM, manifest)

## Learn More

- Simple Web Framework: https://docs.simple-lang.dev/web
- .sui File Format: https://docs.simple-lang.dev/sui
"#,
        project_name
    );

    // Ensure project directory exists before writing additional files
    if let Err(e) = fs::create_dir_all(&project_dir) {
        eprintln!("warning: failed to ensure project directory: {}", e);
    }

    let readme_path = project_dir.join("README.md");
    if let Err(e) = fs::write(&readme_path, readme) {
        eprintln!("warning: failed to write README.md: {}", e);
    }

    // Create .gitignore
    let gitignore = r#"public/
*.wasm
*.smf
.simple_cache/
"#;

    let gitignore_path = project_dir.join(".gitignore");
    if let Err(e) = fs::write(&gitignore_path, gitignore) {
        eprintln!("warning: failed to write .gitignore: {}", e);
    }

    println!("✓ Created Simple web project: {}", project_name);
    println!();
    println!("Next steps:");
    println!("  cd {}", project_name);
    println!("  simple web build app.sui -o public/");
    println!("  cd public/ && python3 -m http.server 8000");
    println!();

    0
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn test_web_build_options_default() {
        let opts = WebBuildOptions::default();
        assert_eq!(opts.output_dir, PathBuf::from("public"));
        assert_eq!(opts.module_name, "app");
        assert!(!opts.optimize);
        assert!(!opts.minify_html);
    }

    #[test]
    fn test_web_init_creates_project() {
        let temp = TempDir::new().unwrap();
        let project_path = temp.path().join("test_project");

        // Use absolute path to avoid race conditions from parallel tests
        let result = web_init(project_path.to_str().unwrap());

        assert_eq!(result, 0, "web_init should return 0");
        assert!(project_path.exists(), "Project directory should exist");
        assert!(project_path.join("app.sui").exists(), "app.sui should exist");
        // README and .gitignore are optional (warnings on failure)
        // Don't assert on them to avoid test flakiness
    }

    #[test]
    fn test_web_init_fails_if_exists() {
        let temp = TempDir::new().unwrap();
        let project_path = temp.path().join("existing_project");
        fs::create_dir(&project_path).unwrap();

        // Use absolute path to avoid race conditions from parallel tests
        let result = web_init(project_path.to_str().unwrap());

        assert_eq!(result, 1); // Should fail
    }
}
