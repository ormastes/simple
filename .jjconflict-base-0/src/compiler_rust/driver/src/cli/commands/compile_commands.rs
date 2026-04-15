//! Compilation command handlers

use std::path::PathBuf;
use simple_common::target::Target;
use simple_compiler::linker::NativeLinker;
use crate::cli::compile::{compile_file, compile_file_native, compile_file_to_ptx, list_linkers, list_targets};
use crate::CompileOptions;

/// Handle 'compile' command - compile source to SMF or native binary
pub fn handle_compile(args: &[String]) -> i32 {
    if args.iter().any(|a| a == "--help" || a == "-h") {
        print_compile_help(false);
        return 0;
    }

    let Some(source) = parse_source_arg(args) else {
        print_compile_help(true);
        return 1;
    };

    let output = args
        .iter()
        .position(|a| a == "-o")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from);

    // Parse flags
    let native = args.iter().any(|a| a == "--native");
    let snapshot = args.iter().any(|a| a == "--snapshot");

    // Parse backend
    let backend = args
        .iter()
        .find(|a| a.starts_with("--backend="))
        .and_then(|a| a.strip_prefix("--backend="))
        .map(|s| s.to_string());

    // CUDA/PTX backend - generate PTX output
    if let Some(ref b) = backend {
        if b == "cuda" || b == "ptx" {
            return compile_file_to_ptx(&source, output);
        }
        if b == "vhdl" {
            eprintln!(
                "error: --backend=vhdl is not supported by the Rust compile frontend; use the Simple compiler entrypoint for VHDL emission"
            );
            return 1;
        }
    }

    // Parse target architecture
    let target = match parse_target_flag(args) {
        Ok(target) => target,
        Err(err) => {
            eprintln!("error: {}", err);
            return 1;
        }
    };

    // Parse linker
    let linker = match parse_linker_flag(args) {
        Ok(linker) => linker,
        Err(err) => {
            eprintln!("error: {}", err);
            return 1;
        }
    };

    // Print linker info if specified
    if let Some(l) = linker {
        if !NativeLinker::is_available(l) {
            eprintln!("warning: linker '{}' not found on system", l.name());
        } else if native {
            println!("Using linker: {}", l.name());
        }
    }

    if native {
        // Parse native binary options
        let layout_optimize = args.iter().any(|a| a == "--layout-optimize");
        let strip = args.iter().any(|a| a == "--strip");
        let pie = !args.iter().any(|a| a == "--no-pie");
        let shared = args.iter().any(|a| a == "--shared");
        let generate_map = args.iter().any(|a| a == "--map");

        compile_file_native(
            &source,
            output,
            target,
            linker,
            layout_optimize,
            strip,
            pie,
            shared,
            generate_map,
        )
    } else {
        // Compile to SMF
        let options = CompileOptions::from_args(args);
        compile_file(&source, output, target, snapshot, options)
    }
}

/// Handle 'targets' command - list available compilation targets
pub fn handle_targets() -> i32 {
    list_targets()
}

/// Handle 'linkers' command - list available native linkers
pub fn handle_linkers() -> i32 {
    list_linkers()
}

fn parse_target_flag(args: &[String]) -> Result<Option<Target>, String> {
    args.iter()
        .enumerate()
        .find_map(|(idx, arg)| {
            if arg == "--target" {
                Some(
                    args.get(idx + 1)
                        .cloned()
                        .ok_or_else(|| "--target requires a value".to_string()),
                )
            } else {
                arg.strip_prefix("--target=").map(|value| Ok(value.to_string()))
            }
        })
        .transpose()?
        .map(|value| Target::parse(&value).map_err(|e| e.to_string()))
        .transpose()
}

fn parse_linker_flag(args: &[String]) -> Result<Option<NativeLinker>, String> {
    args.iter()
        .enumerate()
        .find_map(|(idx, arg)| {
            if arg == "--linker" {
                Some(
                    args.get(idx + 1)
                        .cloned()
                        .ok_or_else(|| "--linker requires a value".to_string()),
                )
            } else {
                arg.strip_prefix("--linker=").map(|value| Ok(value.to_string()))
            }
        })
        .transpose()?
        .map(|s| NativeLinker::from_name(&s).ok_or_else(|| format!("unknown linker '{}'. Available: mold, lld, ld", s)))
        .transpose()
}

fn parse_source_arg(args: &[String]) -> Option<PathBuf> {
    args.iter().skip(1).enumerate().find_map(|(idx, arg)| {
        if arg == "-o" {
            return None;
        }
        if idx > 0 && args[idx] == "-o" {
            return None;
        }
        if arg.starts_with('-') {
            return None;
        }
        Some(PathBuf::from(arg))
    })
}

fn print_compile_help(show_error: bool) {
    if show_error {
        eprintln!("error: compile requires a source file");
    }
    eprintln!(
        "Usage: simple compile <source.spl> [-o <output>] [--native] [--backend=<name>] [--target <target>] [--linker <name>] [--snapshot]"
    );
    eprintln!();
    eprintln!("Options:");
    eprintln!("  -o <output>         Output file (default: source.smf or source for --native)");
    eprintln!("  --native            Compile to standalone native binary (ELF/PE)");
    eprintln!("  --backend=<name>    Backend: cuda/ptx (generate PTX output), vhdl (Simple frontend only)");
    eprintln!("  --target <target>   Target triple or arch (x86_64, aarch64, wasm32-wasi, etc.)");
    eprintln!("  --target=<target>   Same as above");
    eprintln!("  --linker <name>     Native linker to use (mold, lld, ld)");
    eprintln!("  --linker=<name>     Same as above");
    eprintln!("  --layout-optimize   Enable 4KB page layout optimization");
    eprintln!("  --strip             Strip symbols from output");
    eprintln!("  --pie               Create position-independent executable (default)");
    eprintln!("  --no-pie            Disable position-independent executable");
    eprintln!("  --shared            Create shared library (.so/.dll)");
    eprintln!("  --map               Generate linker map file");
    eprintln!("  --snapshot          Create JJ snapshot with build state");
    eprintln!("  --coverage          Enable coverage instrumentation (#674)");
    eprintln!("  --coverage-output=<path>  Output path for coverage report (default: coverage.sdn)");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_target_flag() {
        let args = vec![
            "compile".to_string(),
            "test.spl".to_string(),
            "--target".to_string(),
            "x86_64".to_string(),
        ];
        let target = parse_target_flag(&args).unwrap();
        assert!(target.is_some());
    }

    #[test]
    fn test_parse_target_flag_equals_form() {
        let args = vec![
            "compile".to_string(),
            "test.spl".to_string(),
            "--target=wasm32-wasi".to_string(),
        ];
        let target = parse_target_flag(&args).unwrap().unwrap();
        assert_eq!(target.to_string(), "wasm32-wasi");
    }

    #[test]
    fn test_parse_no_target() {
        let args = vec!["compile".to_string(), "test.spl".to_string()];
        let target = parse_target_flag(&args).unwrap();
        assert!(target.is_none());
    }

    #[test]
    fn test_parse_source_arg_allows_flags_before_source() {
        let args = vec![
            "compile".to_string(),
            "--backend=vhdl".to_string(),
            "test.spl".to_string(),
            "-o".to_string(),
            "out.vhd".to_string(),
        ];
        let source = parse_source_arg(&args);
        assert_eq!(source, Some(PathBuf::from("test.spl")));
    }

    #[test]
    fn test_parse_source_arg_skips_output_value() {
        let args = vec![
            "compile".to_string(),
            "-o".to_string(),
            "out.smf".to_string(),
            "--snapshot".to_string(),
            "test.spl".to_string(),
        ];
        let source = parse_source_arg(&args);
        assert_eq!(source, Some(PathBuf::from("test.spl")));
    }
}
