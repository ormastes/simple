// CLI Dispatch FFI Handler
//
// Implements rt_cli_dispatch_rust for routing commands from Simple to Rust handlers.
// Called when Simple implementation doesn't exist or environment forces Rust.
//
// Phase 1C: Benchmarking and Rust FFI Handler

use simple_driver::cli;

/// Dispatch a command to its Rust handler.
///
/// This is the FFI bridge called from Simple's dispatch system (src/app/cli/dispatch.spl).
///
/// Called when:
/// - Simple implementation doesn't exist (e.g., "test" command)
/// - Simple implementation fails to load/parse
/// - Environment variable forces Rust (e.g., SIMPLE_COMPILE_RUST=1)
/// - Special flags require Rust implementation (e.g., --json, --fix)
///
/// # Arguments
/// * `cmd` - Command name (e.g., "compile", "check", "test")
/// * `args` - Full command-line arguments including command name
/// * `gc_log` - Enable GC logging
/// * `gc_off` - Disable GC
///
/// # Returns
/// Exit code (0 = success, non-zero = error)
///
/// # Performance
/// - Direct match statement (O(1) or O(log n) jump table)
/// - No heap allocations for dispatch
/// - Returns i64 directly (no Result overhead)
#[no_mangle]
pub extern "C" fn rt_cli_dispatch_rust(
    cmd: &str,
    args: &[String],
    gc_log: bool,
    gc_off: bool,
) -> i64 {
    match cmd {
        // =====================================================================
        // Compilation Commands
        // =====================================================================
        "compile" => cli::compile::handle_compile(args),

        "targets" => cli::commands::handle_targets() as i64,

        "linkers" => cli::commands::handle_linkers() as i64,

        "check" => {
            // Check command has custom context wrapper
            let ctx = cli::commands::CommandContext {
                args,
                gc_log,
                gc_off,
            };
            cli::commands::handle_check_wrapper(&ctx)
        }

        // =====================================================================
        // Code Quality
        // =====================================================================
        "lint" => cli::code_quality::run_lint(args) as i64,

        "fix" => cli::code_quality::run_lint(args) as i64, // Same handler

        "fmt" => cli::code_quality::run_fmt(args) as i64,

        // =====================================================================
        // Testing - Always uses Rust (cargo test integration)
        // =====================================================================
        "test" => cli::test_runner::handle_test_rust(args, gc_log, gc_off) as i64,

        // =====================================================================
        // Web Framework
        // =====================================================================
        "web" => cli::commands::handle_web(args),

        // =====================================================================
        // File Watching
        // =====================================================================
        "watch" => {
            if args.len() < 2 {
                eprintln!("error: watch requires a source file");
                eprintln!("Usage: simple watch <file.spl>");
                return 1;
            }
            let path = std::path::PathBuf::from(&args[1]);
            cli::basic::watch_file(&path)
        }

        // =====================================================================
        // Localization
        // =====================================================================
        "i18n" => cli::i18n::run_i18n(args),

        // =====================================================================
        // Migration and Tooling
        // =====================================================================
        "migrate" => cli::migrate::run_migrate(args),

        "mcp" => cli::llm_tools::run_mcp(args),

        "diff" => cli::llm_tools::run_diff(args),

        "context" => cli::llm_tools::run_context(args),

        "constr" => cli::llm_tools::run_constr(args),

        // =====================================================================
        // Analysis and Querying
        // =====================================================================
        "query" => cli::analysis::run_query(args),

        "info" => cli::analysis::run_info(args),

        "spec-coverage" => cli::audit::run_spec_coverage(args),

        "replay" => cli::audit::run_replay(args),

        // =====================================================================
        // Code Generation
        // =====================================================================
        "gen-lean" => cli::gen_lean::run_gen_lean(args),

        "feature-gen" => cli::doc_gen::run_feature_gen(args),

        "task-gen" => cli::doc_gen::run_task_gen(args),

        "spec-gen" => cli::doc_gen::run_spec_gen(args),

        "todo-scan" => cli::doc_gen::run_todo_scan(args),

        "todo-gen" => cli::doc_gen::run_todo_gen(args),

        "sspec-docgen" => cli::sspec_docgen::run_sspec_docgen(args),

        // =====================================================================
        // Documentation
        // =====================================================================
        "brief" => cli::commands::handle_brief(args),

        "dashboard" => cli::commands::handle_dashboard(args),

        // =====================================================================
        // Package Management
        // =====================================================================
        "init" => cli::commands::handle_init(args),

        "install" => cli::commands::handle_install() as i64,

        "publish" => cli::commands::handle_publish(args),

        "add" => cli::commands::handle_add(args),

        "remove" => cli::commands::handle_remove(args),

        "search" => cli::commands::handle_search(args),

        "deps" => cli::commands::handle_deps(args),

        "list" => cli::commands::handle_list() as i64,

        "tree" => cli::commands::handle_tree() as i64,

        // =====================================================================
        // Build System
        // =====================================================================
        "build" => cli::commands::handle_build(args),

        "run" => cli::commands::handle_run(args, gc_log, gc_off),

        "clean" => cli::commands::handle_clean(args),

        // =====================================================================
        // Benchmarking
        // =====================================================================
        "bench" => cli::commands::handle_bench(args),

        // =====================================================================
        // REPL and Execution
        // =====================================================================
        "repl" => cli::repl::run_repl(gc_log, gc_off) as i64,

        "verify" => cli::verify::run_verify(args),

        // =====================================================================
        // Qualification
        // =====================================================================
        "qualify-ignore" => {
            let qi_args = cli::qualify_ignore::parse_qualify_ignore_args(&args[1..]);
            match cli::qualify_ignore::handle_qualify_ignore(qi_args) {
                Ok(()) => 0,
                Err(e) => {
                    eprintln!("error: {}", e);
                    1
                }
            }
        }

        // =====================================================================
        // Unknown Command
        // =====================================================================
        _ => {
            eprintln!("error: unknown command: {}", cmd);
            eprintln!("Run 'simple --help' for usage information");
            1
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dispatch_unknown_command() {
        let args = vec!["simple".to_string(), "invalid-cmd".to_string()];
        let code = rt_cli_dispatch_rust("invalid-cmd", &args, false, false);
        assert_eq!(code, 1);
    }

    #[test]
    fn test_dispatch_targets() {
        let args = vec!["simple".to_string(), "targets".to_string()];
        let code = rt_cli_dispatch_rust("targets", &args, false, false);
        assert_eq!(code, 0);
    }

    #[test]
    fn test_dispatch_linkers() {
        let args = vec!["simple".to_string(), "linkers".to_string()];
        let code = rt_cli_dispatch_rust("linkers", &args, false, false);
        assert_eq!(code, 0);
    }
}
