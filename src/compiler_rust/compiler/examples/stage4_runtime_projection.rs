use simple_compiler::pipeline::native_project::build_stage4_rust_runtime_projection_archive;
use std::path::{Path, PathBuf};

fn read_symbols(path: &Path) -> Result<Vec<String>, String> {
    let content =
        std::fs::read_to_string(path).map_err(|error| format!("failed to read {}: {error}", path.display()))?;
    Ok(content
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(str::to_string)
        .collect())
}

fn main() -> Result<(), String> {
    let args = std::env::args_os().map(PathBuf::from).collect::<Vec<_>>();
    if args.len() != 5 {
        return Err(format!(
            "usage: {} <runtime-archive> <output-dir> <roots-file> <allowed-externals-file>",
            args.first()
                .map(|arg| arg.display().to_string())
                .unwrap_or_else(|| "stage4_runtime_projection".to_string())
        ));
    }
    if args[2].exists() {
        return Err(format!("output directory must not exist: {}", args[2].display()));
    }
    let output = build_stage4_rust_runtime_projection_archive(
        &args[1],
        &read_symbols(&args[3])?,
        &read_symbols(&args[4])?,
        &args[2],
    )?;
    println!("{}", output.display());
    Ok(())
}
