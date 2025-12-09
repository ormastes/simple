//! Simple Language - Unified CLI
//!
//! Usage like Python:
//!   simple              - Start interactive REPL
//!   simple file.spl     - Run source file
//!   simple file.smf     - Run compiled binary
//!   simple -c "code"    - Run code string
//!   simple compile src.spl [-o out.smf]  - Compile to SMF
//!   simple watch file.spl  - Watch and auto-recompile

use std::env;
use std::path::PathBuf;

use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

use simple_driver::runner::Runner;
use simple_driver::watcher::watch;
use simple_log;

const VERSION: &str = "0.1.0";

fn print_help() {
    eprintln!("Simple Language v{}", VERSION);
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  simple                      Start interactive REPL");
    eprintln!("  simple <file.spl>           Run source file");
    eprintln!("  simple <file.smf>           Run compiled binary");
    eprintln!("  simple -c \"code\"            Run code string");
    eprintln!("  simple compile <src> [-o <out>]  Compile to SMF");
    eprintln!("  simple watch <file.spl>     Watch and auto-recompile");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  -h, --help     Show this help");
    eprintln!("  -v, --version  Show version");
    eprintln!("  -c <code>      Run code string");
    eprintln!("  --gc-log       Enable verbose GC logging");
    eprintln!("  --gc=off       Disable garbage collection");
    eprintln!();
    eprintln!("Examples:");
    eprintln!("  simple                      # Start REPL");
    eprintln!("  simple hello.spl            # Run source");
    eprintln!("  simple -c \"main = 42\"       # Run expression");
    eprintln!("  simple compile app.spl      # Compile to app.smf");
    eprintln!("  simple watch app.spl        # Watch for changes");
}

fn print_version() {
    println!("Simple Language v{}", VERSION);
}

fn create_runner(gc_log: bool, gc_off: bool) -> Runner {
    if gc_off {
        Runner::new_no_gc()
    } else if gc_log {
        Runner::new_with_gc_logging()
    } else {
        Runner::new()
    }
}

fn run_repl(gc_log: bool, gc_off: bool) -> i32 {
    println!("Simple Language v{} - Interactive Mode", VERSION);
    println!("Type expressions to evaluate. Use 'exit' or Ctrl-D to quit.");
    println!();

    let runner = create_runner(gc_log, gc_off);
    let mut rl = match DefaultEditor::new() {
        Ok(editor) => editor,
        Err(e) => {
            eprintln!("Failed to initialize REPL: {}", e);
            return 1;
        }
    };

    let history_path = dirs_next::home_dir()
        .map(|h| h.join(".simple_history"))
        .unwrap_or_else(|| PathBuf::from(".simple_history"));

    let _ = rl.load_history(&history_path);

    loop {
        match rl.readline(">>> ") {
            Ok(line) => {
                let line = line.trim();
                if line.is_empty() {
                    continue;
                }
                if line == "exit" || line == "quit" {
                    break;
                }

                let _ = rl.add_history_entry(line);

                // Wrap expression in main if not already a full program
                let code = if line.contains("main") || line.contains("fn ") || line.contains("let ") {
                    line.to_string()
                } else {
                    format!("main = {}", line)
                };

                match runner.run_source_in_memory(&code) {
                    Ok(result) => println!("=> {}", result),
                    Err(e) => eprintln!("Error: {}", e),
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("^C");
                continue;
            }
            Err(ReadlineError::Eof) => {
                println!();
                break;
            }
            Err(e) => {
                eprintln!("Error: {}", e);
                break;
            }
        }
    }

    let _ = rl.save_history(&history_path);
    0
}

fn run_file(path: &PathBuf, gc_log: bool, gc_off: bool) -> i32 {
    let runner = create_runner(gc_log, gc_off);
    match runner.run_file(path) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

fn run_code(code: &str, gc_log: bool, gc_off: bool) -> i32 {
    let runner = create_runner(gc_log, gc_off);

    // Wrap expression in main if not already a full program
    let full_code = if code.contains("main") || code.contains("fn ") || code.contains("let ") {
        code.to_string()
    } else {
        format!("main = {}", code)
    };

    match runner.run_source_in_memory(&full_code) {
        Ok(exit_code) => {
            println!("{}", exit_code);
            exit_code
        }
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

fn compile_file(source: &PathBuf, output: Option<PathBuf>) -> i32 {
    let runner = Runner::new();
    let out_path = output.unwrap_or_else(|| source.with_extension("smf"));

    let source_content = match std::fs::read_to_string(source) {
        Ok(content) => content,
        Err(e) => {
            eprintln!("error: cannot read {}: {}", source.display(), e);
            return 1;
        }
    };

    match runner.compile_to_smf(&source_content, &out_path) {
        Ok(()) => {
            println!("Compiled {} -> {}", source.display(), out_path.display());
            0
        }
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

fn watch_file(path: &PathBuf) -> i32 {
    println!("Watching {} for changes...", path.display());
    println!("Press Ctrl-C to stop.");

    match watch(path, true) {
        Ok(()) => 0,
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

fn main() {
    simple_log::init();

    let args: Vec<String> = env::args().skip(1).collect();

    // Parse global flags
    let gc_log = args.iter().any(|a| a == "--gc-log");
    let gc_off = args.iter().any(|a| a == "--gc=off" || a == "--gc=OFF");

    // Filter out flags
    let args: Vec<String> = args
        .into_iter()
        .filter(|a| !a.starts_with("--gc"))
        .collect();

    // No arguments -> REPL
    if args.is_empty() {
        std::process::exit(run_repl(gc_log, gc_off));
    }

    let first = &args[0];

    // Handle flags
    match first.as_str() {
        "-h" | "--help" => {
            print_help();
            std::process::exit(0);
        }
        "-v" | "--version" => {
            print_version();
            std::process::exit(0);
        }
        "-c" => {
            if args.len() < 2 {
                eprintln!("error: -c requires a code argument");
                std::process::exit(1);
            }
            std::process::exit(run_code(&args[1], gc_log, gc_off));
        }
        "compile" => {
            if args.len() < 2 {
                eprintln!("error: compile requires a source file");
                eprintln!("Usage: simple compile <source.spl> [-o <output.smf>]");
                std::process::exit(1);
            }
            let source = PathBuf::from(&args[1]);
            let output = args.iter()
                .position(|a| a == "-o")
                .and_then(|i| args.get(i + 1))
                .map(PathBuf::from);
            std::process::exit(compile_file(&source, output));
        }
        "watch" => {
            if args.len() < 2 {
                eprintln!("error: watch requires a source file");
                eprintln!("Usage: simple watch <file.spl>");
                std::process::exit(1);
            }
            let path = PathBuf::from(&args[1]);
            std::process::exit(watch_file(&path));
        }
        "run" => {
            // Explicit run command (for compatibility)
            if args.len() < 2 {
                eprintln!("error: run requires a file");
                std::process::exit(1);
            }
            let path = PathBuf::from(&args[1]);
            std::process::exit(run_file(&path, gc_log, gc_off));
        }
        _ => {
            // Assume it's a file to run
            let path = PathBuf::from(first);
            if path.exists() {
                std::process::exit(run_file(&path, gc_log, gc_off));
            } else {
                eprintln!("error: file not found: {}", path.display());
                eprintln!();
                print_help();
                std::process::exit(1);
            }
        }
    }
}
