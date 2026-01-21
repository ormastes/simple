//! Argument parsing for test command.
//!
//! Handles parsing command-line arguments into TestOptions.

use std::path::PathBuf;

use super::types::{TestLevel, OutputFormat, TestOptions};

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
            "--show-tags" => options.show_tags = true,
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
}
