use std::env;
use std::path::PathBuf;

use simple_driver::runner::Runner;
use simple_log;

fn print_usage() {
    eprintln!("Usage: simple-driver run <source.spl> [--gc-log]");
}

fn main() {
    // Initialize tracing/logging once; respects SIMPLE_LOG/RUST_LOG env filters.
    simple_log::init();

    let mut args = env::args().skip(1).collect::<Vec<_>>();
    if args.is_empty() {
        print_usage();
        std::process::exit(1);
    }

    let gc_log = args.contains(&"--gc-log".to_string());
    args.retain(|a| a != "--gc-log");

    let cmd = &args[0];
    match cmd.as_str() {
        "run" => {
            if args.len() < 2 {
                print_usage();
                std::process::exit(1);
            }
            let path = PathBuf::from(&args[1]);
            let runner = if gc_log {
                Runner::new_with_gc_logging()
            } else {
                Runner::new()
            };
            match runner.run_file(&path) {
                Ok(code) => std::process::exit(code),
                Err(e) => {
                    eprintln!("error: {e}");
                    std::process::exit(1);
                }
            }
        }
        _ => {
            print_usage();
            std::process::exit(1);
        }
    }
}
