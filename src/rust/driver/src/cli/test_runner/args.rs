//! Argument parsing for test command.
//!
//! Handles parsing command-line arguments into TestOptions.

use std::path::PathBuf;

use super::types::{TestLevel, TestExecutionMode, OutputFormat, TestOptions};

/// Parse test command arguments
pub fn parse_test_args(args: &[String]) -> TestOptions {
    let mut options = TestOptions::default();
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            "--unit" => options.level = TestLevel::Unit,
            "--integration" => options.level = TestLevel::Integration,
            "--system" => options.level = TestLevel::System,
            "--fail-fast" => options.fail_fast = true,
            "--gc-log" => options.gc_log = true,
            "--gc=off" | "--gc=OFF" => options.gc_off = true,
            "--tag" => {
                i += 1;
                if i < args.len() {
                    options.tag = Some(args[i].clone());
                }
            }
            "--seed" => {
                i += 1;
                if i < args.len() {
                    options.seed = args[i].parse().ok();
                }
            }
            "--format" => {
                i += 1;
                if i < args.len() {
                    options.format = match args[i].as_str() {
                        "json" => OutputFormat::Json,
                        "doc" => OutputFormat::Doc,
                        _ => OutputFormat::Text,
                    };
                }
            }
            "--json" => options.format = OutputFormat::Json,
            "--doc" => options.format = OutputFormat::Doc,
            "--watch" => options.watch = true,
            "--doctest" => {
                options.doctest_src = true;
                options.doctest_doc = true;
                options.doctest_md = true;
            }
            "--all" => {
                // Run everything including all doctests
                options.doctest_src = true;
                options.doctest_doc = true;
                options.doctest_md = true;
            }
            "--doctest-src" => options.doctest_src = true,
            "--doctest-doc" => options.doctest_doc = true,
            "--doctest-md" => options.doctest_md = true,
            "--doctest-src-dir" => {
                i += 1;
                if i < args.len() {
                    options.doctest_src_dir = Some(PathBuf::from(&args[i]));
                    options.doctest_src = true;
                }
            }
            "--doctest-doc-dir" => {
                i += 1;
                if i < args.len() {
                    options.doctest_doc_dir = Some(PathBuf::from(&args[i]));
                    options.doctest_doc = true;
                }
            }
            "--doctest-md-dir" => {
                i += 1;
                if i < args.len() {
                    options.doctest_md_dir = Some(PathBuf::from(&args[i]));
                    options.doctest_md = true;
                }
            }
            // Diagram generation options
            "--seq-diagram" => options.seq_diagram = true,
            "--class-diagram" => options.class_diagram = true,
            "--arch-diagram" => options.arch_diagram = true,
            "--diagram-all" => {
                options.diagram_all = true;
                options.seq_diagram = true;
                options.class_diagram = true;
                options.arch_diagram = true;
            }
            "--seq-include" => {
                i += 1;
                if i < args.len() {
                    options.seq_include = Some(args[i].clone());
                }
            }
            "--seq-exclude" => {
                i += 1;
                if i < args.len() {
                    options.seq_exclude = Some(args[i].clone());
                }
            }
            "--diagram-output" => {
                i += 1;
                if i < args.len() {
                    options.diagram_output = Some(PathBuf::from(&args[i]));
                }
            }
            // Screenshot capture options
            "--capture-screenshots" | "--screenshots" => options.capture_screenshots = true,
            "--refresh-gui-image" | "--refresh-screenshots" => {
                options.refresh_gui_images = true;
                options.capture_screenshots = true;
            }
            "--screenshot-output" => {
                i += 1;
                if i < args.len() {
                    options.screenshot_output = Some(PathBuf::from(&args[i]));
                    options.capture_screenshots = true;
                }
            }
            // Test listing and filtering
            "--list" => options.list = true,
            "--list-ignored" => {
                options.list = true;
                options.list_ignored = true;
            }
            "--only-slow" => options.only_slow = true,
            "--only-skipped" => options.only_skipped = true,
            "--list-skip-features" | "--skip-features" => {
                options.list_skip_features = true;
                options.only_skipped = true; // Need to discover skip files
                options.list = true;
            }
            "--planned-only" | "--pending" => {
                options.skip_features_planned_only = true;
            }
            "--show-tags" => options.show_tags = true,
            // Execution mode
            "--mode" => {
                i += 1;
                if i < args.len() {
                    if let Some(mode) = TestExecutionMode::from_str(&args[i]) {
                        options.execution_mode = mode;
                        // SMF and native modes require safe mode (subprocess execution)
                        if mode != TestExecutionMode::Interpreter {
                            options.safe_mode = true;
                        }
                    } else {
                        eprintln!("Warning: Unknown execution mode '{}', using interpreter", args[i]);
                    }
                }
            }
            arg if arg.starts_with("--mode=") => {
                let mode_str = arg.trim_start_matches("--mode=");
                if let Some(mode) = TestExecutionMode::from_str(mode_str) {
                    options.execution_mode = mode;
                    if mode != TestExecutionMode::Interpreter {
                        options.safe_mode = true;
                    }
                } else {
                    eprintln!("Warning: Unknown execution mode '{}', using interpreter", mode_str);
                }
            }
            "--force-rebuild" => options.force_rebuild = true,
            "--keep-artifacts" => options.keep_artifacts = true,
            "--safe-mode" | "--safe" => options.safe_mode = true,
            "--timeout" => {
                i += 1;
                if i < args.len() {
                    options.safe_mode_timeout = args[i].parse().unwrap_or(30);
                }
            }
            // Parallel execution options
            "--parallel" | "-p" => {
                options.parallel = true;
                options.safe_mode = true; // Parallel requires safe mode
            }
            "--full-parallel" | "-P" => {
                options.full_parallel = true;
                options.parallel = true;
                options.safe_mode = true; // Parallel requires safe mode
            }
            "--threads" | "-j" => {
                i += 1;
                if i < args.len() {
                    options.max_threads = args[i].parse().unwrap_or(0);
                }
            }
            arg if arg.starts_with("--threads=") => {
                options.max_threads = arg.trim_start_matches("--threads=").parse().unwrap_or(0);
            }
            arg if arg.starts_with("-j") && arg.len() > 2 => {
                // Handle -j4 style (no space)
                options.max_threads = arg[2..].parse().unwrap_or(0);
            }
            "--cpu-threshold" => {
                i += 1;
                if i < args.len() {
                    options.cpu_threshold = args[i].parse().unwrap_or(70);
                }
            }
            arg if arg.starts_with("--cpu-threshold=") => {
                options.cpu_threshold = arg.trim_start_matches("--cpu-threshold=").parse().unwrap_or(70);
            }
            "--memory-threshold" => {
                i += 1;
                if i < args.len() {
                    options.memory_threshold = args[i].parse().unwrap_or(70);
                }
            }
            arg if arg.starts_with("--memory-threshold=") => {
                options.memory_threshold = arg.trim_start_matches("--memory-threshold=").parse().unwrap_or(70);
            }
            "--throttled-threads" => {
                i += 1;
                if i < args.len() {
                    options.throttled_threads = args[i].parse().unwrap_or(1);
                }
            }
            arg if arg.starts_with("--throttled-threads=") => {
                options.throttled_threads = arg.trim_start_matches("--throttled-threads=").parse().unwrap_or(1);
            }
            "--cpu-check-interval" => {
                i += 1;
                if i < args.len() {
                    options.cpu_check_interval = args[i].parse().unwrap_or(5);
                }
            }
            // Rust test tracking
            "--rust-tests" => options.rust_tests = true,
            "--rust-ignored" => {
                options.rust_tests = true;
                options.rust_ignored_only = true;
            }
            // Run management options
            "--list-runs" => options.list_runs = true,
            "--cleanup-runs" => options.cleanup_runs = true,
            "--prune-runs" => {
                i += 1;
                if i < args.len() {
                    options.prune_runs = args[i].parse().ok();
                } else {
                    // Default to keeping 100 runs
                    options.prune_runs = Some(100);
                }
            }
            arg if arg.starts_with("--prune-runs=") => {
                options.prune_runs = arg.trim_start_matches("--prune-runs=").parse().ok();
            }
            "--runs-status" => {
                i += 1;
                if i < args.len() {
                    options.runs_status_filter = Some(args[i].clone());
                }
            }
            arg if arg.starts_with("--runs-status=") => {
                options.runs_status_filter = Some(arg.trim_start_matches("--runs-status=").to_string());
            }
            arg if !arg.starts_with("-") && options.path.is_none() => {
                options.path = Some(PathBuf::from(arg));
            }
            _ => {}
        }
        i += 1;
    }

    options
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_basic_flags() {
        let args = vec!["--unit".to_string(), "--fail-fast".to_string()];
        let opts = parse_test_args(&args);
        assert_eq!(opts.level, TestLevel::Unit);
        assert!(opts.fail_fast);
    }

    #[test]
    fn test_parse_format() {
        let args = vec!["--format".to_string(), "json".to_string()];
        let opts = parse_test_args(&args);
        assert_eq!(opts.format, OutputFormat::Json);
    }

    #[test]
    fn test_parse_diagram_all() {
        let args = vec!["--diagram-all".to_string()];
        let opts = parse_test_args(&args);
        assert!(opts.seq_diagram);
        assert!(opts.class_diagram);
        assert!(opts.arch_diagram);
        assert!(opts.diagram_all);
    }

    #[test]
    fn test_parse_path() {
        let args = vec!["test/my_test.spl".to_string()];
        let opts = parse_test_args(&args);
        assert_eq!(opts.path, Some(PathBuf::from("test/my_test.spl")));
    }

    #[test]
    fn test_parse_parallel_flags() {
        let args = vec!["--parallel".to_string()];
        let opts = parse_test_args(&args);
        assert!(opts.parallel);
        assert!(opts.safe_mode); // Parallel enables safe mode
    }

    #[test]
    fn test_parse_full_parallel() {
        let args = vec!["--full-parallel".to_string()];
        let opts = parse_test_args(&args);
        assert!(opts.full_parallel);
        assert!(opts.parallel);
        assert!(opts.safe_mode);
    }

    #[test]
    fn test_parse_threads() {
        let args = vec!["--threads".to_string(), "4".to_string()];
        let opts = parse_test_args(&args);
        assert_eq!(opts.max_threads, 4);

        // Test --threads=N format
        let args = vec!["--threads=8".to_string()];
        let opts = parse_test_args(&args);
        assert_eq!(opts.max_threads, 8);

        // Test -j4 format
        let args = vec!["-j4".to_string()];
        let opts = parse_test_args(&args);
        assert_eq!(opts.max_threads, 4);
    }

    #[test]
    fn test_parse_cpu_threshold() {
        let args = vec!["--cpu-threshold".to_string(), "50".to_string()];
        let opts = parse_test_args(&args);
        assert_eq!(opts.cpu_threshold, 50);

        let args = vec!["--cpu-threshold=80".to_string()];
        let opts = parse_test_args(&args);
        assert_eq!(opts.cpu_threshold, 80);
    }

    #[test]
    fn test_parse_memory_threshold() {
        let args = vec!["--memory-threshold".to_string(), "60".to_string()];
        let opts = parse_test_args(&args);
        assert_eq!(opts.memory_threshold, 60);

        let args = vec!["--memory-threshold=85".to_string()];
        let opts = parse_test_args(&args);
        assert_eq!(opts.memory_threshold, 85);
    }

    #[test]
    fn test_parse_throttled_threads() {
        let args = vec!["--throttled-threads".to_string(), "2".to_string()];
        let opts = parse_test_args(&args);
        assert_eq!(opts.throttled_threads, 2);

        let args = vec!["--throttled-threads=3".to_string()];
        let opts = parse_test_args(&args);
        assert_eq!(opts.throttled_threads, 3);
    }

    #[test]
    fn test_parse_rust_tests() {
        let args = vec!["--rust-tests".to_string()];
        let opts = parse_test_args(&args);
        assert!(opts.rust_tests);
        assert!(!opts.rust_ignored_only);
    }

    #[test]
    fn test_parse_rust_ignored() {
        let args = vec!["--rust-ignored".to_string()];
        let opts = parse_test_args(&args);
        assert!(opts.rust_tests);
        assert!(opts.rust_ignored_only);
    }
}
