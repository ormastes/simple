//! Web framework command handlers

use std::path::PathBuf;
use crate::cli::web::{web_build, web_features, web_init, web_serve, WebBuildOptions, WebServeOptions};

/// Handle 'web' command - web framework operations
pub fn handle_web(args: &[String]) -> i32 {
    if args.len() < 2 {
        print_web_help();
        return 1;
    }

    match args[1].as_str() {
        "build" => handle_web_build(args),
        "init" => handle_web_init(args),
        "features" => web_features(),
        "serve" => handle_web_serve(args),
        _ => {
            eprintln!("error: unknown web subcommand '{}'", args[1]);
            eprintln!("Available: build, init, features, serve");
            1
        }
    }
}

fn handle_web_build(args: &[String]) -> i32 {
    if args.len() < 3 {
        eprintln!("error: web build requires a .sui file");
        eprintln!("Usage: simple web build <file.sui> [options]");
        return 1;
    }

    let source = PathBuf::from(&args[2]);

    // Parse options
    let output_dir = args
        .iter()
        .position(|a| a == "-o" || a == "--output")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("public"));

    let module_name = args
        .iter()
        .position(|a| a == "--module")
        .and_then(|i| args.get(i + 1))
        .map(|s| s.to_string())
        .unwrap_or_else(|| "app".to_string());

    let optimize = args.iter().any(|a| a == "--optimize");
    let minify_html = args.iter().any(|a| a == "--minify");

    let options = WebBuildOptions {
        output_dir,
        module_name,
        optimize,
        minify_html,
    };

    web_build(&source, options)
}

fn handle_web_init(args: &[String]) -> i32 {
    if args.len() < 3 {
        eprintln!("error: web init requires a project name");
        eprintln!("Usage: simple web init <project-name>");
        return 1;
    }

    let project_name = &args[2];
    web_init(project_name)
}

fn handle_web_serve(args: &[String]) -> i32 {
    if args.len() < 3 {
        eprintln!("error: web serve requires a .sui file");
        eprintln!("Usage: simple web serve <file.sui> [options]");
        return 1;
    }

    let source = PathBuf::from(&args[2]);

    // Parse build options
    let output_dir = args
        .iter()
        .position(|a| a == "-o" || a == "--output")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("public"));

    let module_name = args
        .iter()
        .position(|a| a == "--module")
        .and_then(|i| args.get(i + 1))
        .map(|s| s.to_string())
        .unwrap_or_else(|| "app".to_string());

    let build_options = WebBuildOptions {
        output_dir,
        module_name,
        optimize: false, // Dev server: no optimization for speed
        minify_html: false,
    };

    // Parse serve options
    let port = args
        .iter()
        .position(|a| a == "-p" || a == "--port")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse::<u16>().ok())
        .unwrap_or(8000);

    let watch = !args.iter().any(|a| a == "--no-watch");
    let open = args.iter().any(|a| a == "--open");

    let serve_options = WebServeOptions { port, watch, open };

    web_serve(&source, build_options, serve_options)
}

fn print_web_help() {
    eprintln!("Simple Web Framework - Compile .sui files to HTML + WASM");
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  simple web build <file.sui> [options]  - Build web application");
    eprintln!("  simple web serve <file.sui> [options]  - Start development server");
    eprintln!("  simple web init <name>                 - Create new web project");
    eprintln!("  simple web features                    - List supported features");
    eprintln!();
    eprintln!("Build options:");
    eprintln!("  -o, --output <dir>     Output directory (default: public/)");
    eprintln!("  --module <name>        WASM module name (default: app)");
    eprintln!("  --optimize             Optimize WASM binary");
    eprintln!("  --minify               Minify HTML output");
    eprintln!();
    eprintln!("Serve options:");
    eprintln!("  -p, --port <port>      Port number (default: 8000)");
    eprintln!("  --no-watch             Disable file watching");
    eprintln!("  --open                 Open browser automatically");
    eprintln!();
}
