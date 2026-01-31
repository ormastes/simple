//! Compilation command handlers

use std::path::PathBuf;
use simple_common::target::{Target, TargetArch};
use simple_compiler::linker::NativeLinker;
use crate::cli::compile::{compile_file, compile_file_native, list_linkers, list_targets};
use crate::CompileOptions;

/// Handle 'compile' command - compile source to SMF or native binary
pub fn handle_compile(args: &[String]) -> i32 {
    if args.len() < 2 {
        print_compile_help();
        return 1;
    }

    let source = PathBuf::from(&args[1]);
    let output = args
        .iter()
        .position(|a| a == "-o")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from);

    // Parse flags
    let native = args.iter().any(|a| a == "--native");
    let snapshot = args.iter().any(|a| a == "--snapshot");

    // Parse target architecture
    let target = parse_target_flag(args);

    // Parse linker
    let linker = parse_linker_flag(args);

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

fn parse_target_flag(args: &[String]) -> Option<Target> {
    args.iter()
        .position(|a| a == "--target")
        .and_then(|i| args.get(i + 1))
        .map(|s| {
            s.parse::<TargetArch>()
                .map_err(|e| {
                    eprintln!("error: {}", e);
                    std::process::exit(1);
                })
                .unwrap()
        })
        .map(|arch| Target::new(arch, simple_common::target::TargetOS::host()))
}

fn parse_linker_flag(args: &[String]) -> Option<NativeLinker> {
    args.iter()
        .position(|a| a == "--linker")
        .and_then(|i| args.get(i + 1))
        .map(|s| {
            NativeLinker::from_name(s).unwrap_or_else(|| {
                eprintln!("error: unknown linker '{}'. Available: mold, lld, ld", s);
                std::process::exit(1);
            })
        })
}

fn print_compile_help() {
    eprintln!("error: compile requires a source file");
    eprintln!(
        "Usage: simple compile <source.spl> [-o <output>] [--native] [--target <arch>] [--linker <name>] [--snapshot]"
    );
    eprintln!();
    eprintln!("Options:");
    eprintln!("  -o <output>         Output file (default: source.smf or source for --native)");
    eprintln!("  --native            Compile to standalone native binary (ELF/PE)");
    eprintln!("  --target <arch>     Target architecture (x86_64, aarch64, etc.)");
    eprintln!("  --linker <name>     Native linker to use (mold, lld, ld)");
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
        let target = parse_target_flag(&args);
        assert!(target.is_some());
    }

    #[test]
    fn test_parse_no_target() {
        let args = vec!["compile".to_string(), "test.spl".to_string()];
        let target = parse_target_flag(&args);
        assert!(target.is_none());
    }
}
