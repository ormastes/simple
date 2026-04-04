//! Help and version information for the Simple CLI.

/// Version from VERSION file (set by build.rs), falls back to Cargo.toml
const VERSION: &str = match option_env!("SIMPLE_VERSION") {
    Some(v) if !v.is_empty() => v,
    _ => env!("CARGO_PKG_VERSION"),
};

pub fn print_help() {
    eprintln!("Simple Language v{}", VERSION);
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  simple                      Start interactive TUI REPL (default)");
    eprintln!("  simple --notui              Start Normal REPL (rustyline-based)");
    eprintln!("  simple <file.spl>           Run source file");
    eprintln!("  simple <file.smf>           Run compiled binary");
    eprintln!("  simple -c \"code\"            Run code string");
    eprintln!("  simple compile <src> [-o <out>] [options]  Compile source file");
    eprintln!("  simple watch <file.spl>     Watch and auto-recompile");
    eprintln!("  simple examples-check [path] [--compile|--run] [--timeout <secs>]");
    eprintln!("                            Validate examples one by one with per-file isolation");
    eprintln!("  files under examples/       Run with automatic timeout safety defaults");
    eprintln!("  simple targets              List available target architectures");
    eprintln!("  simple linkers              List available native linkers");
    eprintln!();
    eprintln!("Testing:");
    eprintln!("  simple test [path]          Run tests (default: test/)");
    eprintln!("  simple test --unit          Run unit tests only");
    eprintln!("  simple test --integration   Run integration tests only");
    eprintln!("  simple test --system        Run system tests only");
    eprintln!("  simple test --tag <name>    Filter by tag");
    eprintln!("  simple test --fail-fast     Stop on first failure");
    eprintln!("  simple test --seed <N>      Deterministic shuffle");
    eprintln!("  simple test --format <fmt>  Output format: text, json, doc");
    eprintln!("  simple test --json          Shorthand for --format json");
    eprintln!("  simple test --doc           Shorthand for --format doc");
    eprintln!("  simple test --watch         Watch and auto-rerun on changes");
    eprintln!("  simple test --seq-diagram   Generate sequence diagrams from tests");
    eprintln!("  simple test --class-diagram Generate class diagrams from tests");
    eprintln!("  simple test --arch-diagram  Generate architecture diagrams from tests");
    eprintln!("  simple test --diagram-all   Generate all diagram types");
    eprintln!("  simple test --list-skip-features   List features from .skip files");
    eprintln!("  simple test --planned-only  Filter to planned features only");
    eprintln!();
    eprintln!("Diagram Generation:");
    eprintln!("  simple diagram -A -n my_test      Generate all diagrams");
    eprintln!("  simple diagram -s --include \"*Service\"   Sequence with filter");
    eprintln!("  simple diagram --help             Show diagram options");
    eprintln!();
    eprintln!("Code Quality:");
    eprintln!("  simple lint [path]          Run linter on file or directory");
    eprintln!("  simple lint --json          Output lint results as JSON");
    eprintln!("  simple lint --fix           Apply auto-fixes");
    eprintln!("  simple fmt [path]           Format file or directory");
    eprintln!("  simple fmt --check          Check formatting without changes");
    eprintln!();
    eprintln!("Internationalization (i18n):");
    eprintln!("  simple i18n extract [path]      Extract i18n strings to locale files");
    eprintln!("  simple i18n generate <locale>   Generate locale template (e.g., ko-KR)");
    eprintln!("  simple i18n --help              Show i18n help");
    eprintln!();
    eprintln!("LLM-Friendly Tools:");
    eprintln!("  simple mcp <file.spl>       Generate minimal code preview (90% token reduction)");
    eprintln!("  simple mcp <file.spl> --expand <symbol>  Expand specific symbol");
    eprintln!("  simple mcp <file.spl> --search <query>   Search for symbols");
    eprintln!("  simple mcp <file.spl> --show-coverage    Show coverage overlays");
    eprintln!("  simple diff <old.spl> <new.spl> --semantic  Semantic diff (compare AST/HIR)");
    eprintln!("  simple diff <old.spl> <new.spl> --json     Output diff as JSON");
    eprintln!("  simple context <file.spl> [target]  Extract minimal context pack");
    eprintln!("  simple context <file.spl> --minimal     Only direct dependencies");
    eprintln!("  simple context <file.spl> --json        Output as JSON");
    eprintln!("  simple context <file.spl> --markdown    Output as Markdown");
    eprintln!();
    eprintln!("Documentation Generation:");
    eprintln!("  simple sspec-docgen <files...>           Generate docs from SSpec test files");
    eprintln!("  simple sspec-docgen <files...> -o <dir>  Output to specific directory");
    eprintln!("  simple ffi-gen <file.spl> [options]      Generate FFI wrappers from @Lib extern declarations");
    eprintln!();
    eprintln!("Build & Audit (#911-915):");
    eprintln!("  simple query --generated           Find all LLM-generated code");
    eprintln!("  simple query --generated --unverified    Find unverified generated code");
    eprintln!("  simple query --generated-by=<tool>       Find code by specific tool");
    eprintln!("  simple info <function> --provenance      Show provenance metadata");
    eprintln!("  simple spec-coverage                     Show specification coverage");
    eprintln!("  simple spec-coverage --by-category       Coverage by category");
    eprintln!("  simple spec-coverage --missing           Show missing features");
    eprintln!("  simple spec-coverage --report=html       Generate HTML report");
    eprintln!("  simple replay <log.json>                 Display build log");
    eprintln!("  simple replay --compare <log1> <log2>    Compare two builds");
    eprintln!("  simple replay --extract-errors <log>     Extract diagnostics");
    eprintln!();
    eprintln!("Verification (Lean Code Generation):");
    eprintln!("  simple gen-lean generate           Generate all Lean verification files");
    eprintln!("  simple gen-lean compare            Compare generated with existing Lean files");
    eprintln!("  simple gen-lean compare --diff     Show unified diff for differences");
    eprintln!("  simple gen-lean write              Write regenerated files (safe, won't overwrite)");
    eprintln!("  simple gen-lean write --force      Overwrite existing Lean files");
    eprintln!("  simple gen-lean verify             Run the Lean proof checker");
    eprintln!("  simple gen-lean --project <name>   Generate specific project only");
    eprintln!();
    eprintln!("Verification Management:");
    eprintln!("  simple verify status               Show Lean availability and file status");
    eprintln!("  simple verify regenerate           Regenerate Lean files from verification models");
    eprintln!("  simple verify check                Check all proof obligations and fail on sorry");
    eprintln!("  simple verify list                 List verification files and their state");
    eprintln!("  simple verify quality [--all] [file ...]  Audit anti-dummy / anti-stub quality");
    eprintln!();
    eprintln!("Dashboard & Metrics:");
    eprintln!("  simple dashboard                   Show project metrics dashboard");
    eprintln!("  simple dashboard collect           Collect fresh metrics data");
    eprintln!("  simple dashboard status            Show dashboard summary");
    eprintln!("  simple dashboard cache-stats       Show cache statistics");
    eprintln!();
    eprintln!("Package Management:");
    eprintln!("  simple init [name]          Create a new project");
    eprintln!("  simple add <pkg> [options]  Add a dependency");
    eprintln!("  simple remove <pkg>         Remove a dependency");
    eprintln!("  simple install              Install all dependencies");
    eprintln!("  simple update [pkg]         Update dependencies");
    eprintln!("  simple list                 List installed dependencies");
    eprintln!("  simple tree                 Show dependency tree");
    eprintln!();
    eprintln!("Cache Management:");
    eprintln!("  simple cache info           Show cache information");
    eprintln!("  simple cache list           List cached packages");
    eprintln!("  simple cache clean          Clear the cache");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  -h, --help     Show this help");
    eprintln!("  -v, --version  Show version");
    eprintln!("  -c <code>      Run code string");
    eprintln!("  --notui        Use Normal REPL instead of TUI (TUI is default)");
    eprintln!("  --gc-log       Enable verbose GC logging");
    eprintln!("  --gc=off       Disable garbage collection");
    eprintln!("  --macro-trace  Enable macro expansion tracing");
    eprintln!("  --debug        Enable debug mode (dprint statements will output)");
    eprintln!("  --lang <code>  Set output language for diagnostics (e.g., ko, ja)");
    eprintln!("  --target <arch>  Target architecture for cross-compilation");
    eprintln!("  --linker <name>  Native linker: mold, lld, ld (auto-detected if not set)");
    eprintln!("  --snapshot     Create JJ snapshot on successful build/test");
    eprintln!();
    eprintln!("Sandboxed Execution (#916-919):");
    eprintln!("  --sandbox               Enable sandboxing with default limits");
    eprintln!("  --time-limit <secs>     Set CPU time limit (seconds)");
    eprintln!("  --memory-limit <bytes>  Set memory limit (bytes, accepts K/M/G suffix)");
    eprintln!("  --fd-limit <count>      Set file descriptor limit");
    eprintln!("  --thread-limit <count>  Set thread limit");
    eprintln!("  --no-network            Block all network access");
    eprintln!("  --network-allow <domains>  Allow specific domains (comma-separated)");
    eprintln!("  --network-block <domains>  Block specific domains (comma-separated)");
    eprintln!("  --read-only <paths>     Restrict filesystem to read-only paths (comma-separated)");
    eprintln!("  --read-write <paths>    Restrict filesystem to specific read-write paths (comma-separated)");
    eprintln!();
    eprintln!("Build Optimization (#824):");
    eprintln!("  --parallel     Enable parallel compilation (uses all CPU cores)");
    eprintln!("  --parallel=N   Use N threads for parallel compilation");
    eprintln!("  --profile      Show compilation profiling information");
    eprintln!("  --mmap         Force memory-mapped file reading");
    eprintln!("  --no-mmap      Disable memory-mapped file reading");
    eprintln!();
    eprintln!("IR Export (LLM-friendly #885-887):");
    eprintln!("  --emit-ast     Export AST to stdout");
    eprintln!("  --emit-ast=<file>  Export AST to file");
    eprintln!("  --emit-hir     Export HIR to stdout");
    eprintln!("  --emit-hir=<file>  Export HIR to file");
    eprintln!("  --emit-mir     Export MIR to stdout");
    eprintln!("  --emit-mir=<file>  Export MIR to file");
    eprintln!();
    eprintln!("Deterministic Builds (#911) & Replay Logs (#912):");
    eprintln!("  --deterministic              Enable deterministic build mode");
    eprintln!("  --build-timestamp=<ISO8601>  Override build timestamp (e.g., 2025-01-15T10:00:00Z)");
    eprintln!("  --log=<file.json>            Save build log for replay and debugging");
    eprintln!();
    eprintln!("Runner Memory Limits:");
    eprintln!("  --memory-limit=<size>        Set memory limit per runner thread (default: 1G)");
    eprintln!("                               Accepts: bytes, K/KB, M/MB, G/GB (e.g., 512M, 2G)");
    eprintln!("  --unlimited-memory           Disable memory limit (no limit)");
    eprintln!("  --no-memory-limit            Same as --unlimited-memory");
    eprintln!("  --memory-warn-only           Warn instead of fail on limit exceeded");
    eprintln!();
    eprintln!("Target Architectures:");
    eprintln!("  x86_64   64-bit x86 (default on most systems)");
    eprintln!("  aarch64  64-bit ARM (Apple Silicon, ARM servers)");
    eprintln!("  i686     32-bit x86");
    eprintln!("  armv7    32-bit ARM");
    eprintln!("  riscv64  64-bit RISC-V");
    eprintln!("  riscv32  32-bit RISC-V");
    eprintln!();
    eprintln!("Add Options:");
    eprintln!("  --path <path>  Add as path dependency");
    eprintln!("  --git <url>    Add as git dependency");
    eprintln!("  --branch <br>  Git branch (with --git)");
    eprintln!("  --dev          Add as dev dependency");
    eprintln!();
    eprintln!("Examples:");
    eprintln!("  simple                      # Start REPL");
    eprintln!("  simple hello.spl            # Run source");
    eprintln!("  simple -c \"main = 42\"       # Run expression");
    eprintln!("  simple compile app.spl      # Compile to app.smf");
    eprintln!("  simple compile app.spl --target aarch64  # Cross-compile");
    eprintln!("  simple compile app.spl --snapshot  # Compile and snapshot");
    eprintln!("  simple watch app.spl        # Watch for changes");
    eprintln!("  simple init myapp           # Create new project");
    eprintln!("  simple add http \"1.0\"       # Add dependency");
    eprintln!("  simple add mylib --path ../mylib  # Add local dep");
    eprintln!();
    eprintln!("Sandbox Examples:");
    eprintln!("  simple script.spl --sandbox                    # Run with default sandbox");
    eprintln!("  simple script.spl --time-limit 30              # 30 second CPU limit");
    eprintln!("  simple script.spl --memory-limit 100M          # 100 MB memory limit");
    eprintln!("  simple script.spl --no-network                 # Block all network");
    eprintln!("  simple script.spl --network-allow github.com   # Allow only GitHub");
    eprintln!("  simple script.spl --read-only /tmp,/usr/lib    # Read-only filesystem");
    eprintln!("  simple script.spl --sandbox --time-limit 60 --memory-limit 256M  # Combined");
}

pub fn print_ffi_gen_help() {
    eprintln!("FFI Wrapper Generator");
    eprintln!("=====================");
    eprintln!();
    eprintln!("Generates Rust/C wrapper code from @Lib annotated extern class declarations.");
    eprintln!("The Rust build environment is set up at build/rust/ from simple.sdn config");
    eprintln!("and persists across runs to avoid toolchain setup overhead.");
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  simple ffi-gen <file.spl> [OPTIONS]");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  --output=<dir>    Output directory (default: build/rust/ffi_gen/)");
    eprintln!("  --dry-run         Print generated code without writing");
    eprintln!("  --verbose         Verbose logging");
    eprintln!("  --lang=<lang>     Filter by language: rust, c");
    eprintln!("  --gen-intern      Generate interpreter_extern Rust module from spec");
    eprintln!("  --gen-all         Generate entire build/rust/ from all full specs");
    eprintln!("  --gen-module      Generate a single module from a full spec file");
    eprintln!("  --gen-workspace   Generate multi-crate workspace (16 FFI crates)");
    eprintln!("  --verify          Verify generated code compiles (cargo check)");
    eprintln!("  --clean           Clean build/rust/ and re-setup from scratch");
    eprintln!("  -h, --help        Show this help");
}

pub fn test_help_text() -> String {
    format!(
        "Simple Test Runner v{VERSION}\n\
\n\
Usage:\n\
  simple test [path] [options]\n\
\n\
Filters:\n\
  --unit                  Run unit tests only\n\
  --integration           Run integration tests only\n\
  --system                Run system tests only\n\
  --tag <name>            Filter by tag\n\
  --only-slow             Run slow tests only\n\
  --only-skipped          Run skipped tests only\n\
\n\
Output:\n\
  --list                  List tests without running them\n\
  --list-ignored          List ignored tests only\n\
  --format <text|json|doc>\n\
  --json                  Shorthand for --format json\n\
  --doc                   Shorthand for --format doc\n\
  --watch                 Watch and auto-rerun on changes\n\
  --screenshots           Capture GUI screenshots for tagged tests\n\
  --refresh-screenshots   Force recapture of GUI screenshots\n\
  --screenshot-output <dir>  Screenshot output directory (default: doc/spec/image)\n\
\n\
Doctests:\n\
  --doctest, --sdoctest   Run all doctest modes\n\
  --doctest-src           Run src doctests\n\
  --doctest-doc           Run doc/ doctests\n\
  --doctest-md            Run README-style markdown doctests\n\
  --doctest-src-dir <dir>\n\
  --doctest-doc-dir <dir>\n\
  --doctest-md-dir <dir>\n\
\n\
Execution:\n\
  --mode <interpreter|smf|native>\n\
  --parallel, -p          Enable parallel execution\n\
  --sequential            Force sequential execution\n\
  --threads, -j <N>       Set worker threads\n\
  --timeout <sec>         Safe-mode timeout\n\
  --fail-fast             Stop on first failure\n\
\n\
Run Management:\n\
  --list-runs             Show tracked test runs\n\
  --cleanup-runs          Mark stale/dead runs as crashed\n\
  --prune-runs <N>        Keep only the most recent N runs\n\
  --runs-status <status>  Filter listed runs by status\n\
\n\
Examples:\n\
  simple test\n\
  simple test test/unit/\n\
  simple test --sdoctest README.md\n\
  simple test --list-runs\n"
    )
}

pub fn print_test_help() {
    eprint!("{}", test_help_text());
}

#[cfg(test)]
mod tests {
    use super::test_help_text;

    #[test]
    fn test_test_help_mentions_doctest_and_run_management_flags() {
        let help = test_help_text();
        assert!(help.contains("--sdoctest"));
        assert!(help.contains("--list-runs"));
        assert!(help.contains("--screenshots"));
        assert!(help.contains("doc/spec/image"));
        assert!(help.contains("simple test [path] [options]"));
    }
}

pub fn print_version() {
    println!("Simple Language v{}", VERSION);
}

pub fn version() -> &'static str {
    VERSION
}
