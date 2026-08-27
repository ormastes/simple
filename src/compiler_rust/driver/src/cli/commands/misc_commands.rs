//! Miscellaneous command handlers (diagram, lock, run, etc.)

use std::path::{Path, PathBuf};
use crate::cli::diagram_gen::{generate_diagrams_from_events, parse_diagram_args, print_diagram_help};
use crate::cli::lock;

/// Handle 'diagram' command - generate UML diagrams from profile data
pub fn handle_diagram(args: &[String]) -> i32 {
    // Check for help
    if args.iter().any(|a| a == "-h" || a == "--help") {
        print_diagram_help();
        return 0;
    }

    // Parse diagram generation options
    let diagram_args: Vec<String> = args[1..].to_vec();
    let options = parse_diagram_args(&diagram_args);

    // Check if we have a profile file to load
    if let Some(ref profile_path) = options.from_file {
        // Load profile data from file
        match simple_compiler::runtime_profile::ProfileData::load_from_file(profile_path) {
            Ok(profile_data) => {
                println!(
                    "Loaded profile: {} ({} events)",
                    profile_data.name,
                    profile_data.events.len()
                );

                // Generate diagrams from the loaded profile data
                let architectural = profile_data.get_architectural_entities();
                match generate_diagrams_from_events(profile_data.get_events(), &architectural, &options) {
                    Ok(result) => {
                        if let Some(path) = result.sequence_path {
                            println!("  Sequence diagram: {}", path.display());
                        }
                        if let Some(path) = result.class_path {
                            println!("  Class diagram: {}", path.display());
                        }
                        if let Some(path) = result.arch_path {
                            println!("  Architecture diagram: {}", path.display());
                        }
                        println!("Diagrams generated successfully.");
                        0
                    }
                    Err(e) => {
                        eprintln!("error: failed to generate diagrams: {}", e);
                        1
                    }
                }
            }
            Err(e) => {
                eprintln!("error: {}", e);
                1
            }
        }
    } else {
        // No profile file specified - show usage help
        print_diagram_usage(&options);
        0
    }
}

fn print_diagram_usage(options: &crate::cli::diagram_gen::DiagramGenOptions) {
    println!("Diagram generation options:");
    println!("  Types: {:?}", options.diagram_types);
    println!("  Output: {}", options.output_dir.display());
    println!("  Name: {}", options.test_name);
    if !options.include_patterns.is_empty() {
        println!("  Include: {:?}", options.include_patterns);
    }
    if !options.exclude_patterns.is_empty() {
        println!("  Exclude: {:?}", options.exclude_patterns);
    }

    println!();
    println!("No profile file specified. Usage:");
    println!("  simple diagram <profile.json>           Load and generate diagrams");
    println!("  simple diagram -f <file> -A             Generate all diagram types");
    println!();
    println!("To record profile data, use:");
    println!("  simple test --seq-diagram my_test.spl");
}

/// Handle 'lock' command - manage lock files
pub fn handle_lock(args: &[String]) -> i32 {
    let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let check_only = args.iter().any(|a| a == "--check");
    let info_only = args.iter().any(|a| a == "--info");

    if info_only {
        lock::lock_info(&dir)
    } else if check_only {
        lock::check_lock(&dir)
    } else {
        lock::generate_lock(&dir)
    }
}

/// Handle 'run' command - explicit run command for compatibility
pub fn handle_run(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    if args.len() < 2 {
        eprintln!("error: run requires a file");
        return 1;
    }
    let requested_path = PathBuf::from(&args[1]);
    let path = match crate::cli::basic::resolve_existing_input_path(&requested_path) {
        Some(path) => path,
        None => requested_path,
    };
    let mut file_args = vec![args[1].clone()];
    if args.len() > 2 {
        file_args.extend(args[2..].iter().cloned());
    }
    crate::cli::basic::run_file_with_args(&path, gc_log, gc_off, file_args)
}

/// Handle 'build' command - build system (bootstrap, lint, fmt, check, etc.)
pub fn handle_build(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    let sub_args: Vec<&str> = if args.len() > 1 {
        args[1..].iter().map(|s| s.as_str()).collect()
    } else {
        vec![]
    };

    let cmd = sub_args.first().copied().unwrap_or("help");

    match cmd {
        "bootstrap" => handle_bootstrap(&sub_args[1..]),
        "lint" => handle_build_lint_with_args(&sub_args[1..]),
        "fmt" => handle_build_fmt(&sub_args[1..]),
        "check" => handle_build_check(),
        "help" | "--help" | "-h" => {
            println!("Simple Build System");
            println!();
            println!("USAGE:");
            println!("  simple build <command> [options]");
            println!();
            println!("COMMANDS:");
            println!("  bootstrap      3-stage self-compilation verification");
            println!("  lint           Run clippy linter on Rust workspace");
            println!("  fmt            Run rustfmt on Rust workspace");
            println!("  check          Run lint + fmt --check + tests");
            println!("  help           Show this help");
            println!();
            println!("FMT OPTIONS:");
            println!("  --check            Check formatting without modifying files");
            println!();
            println!("LINT OPTIONS:");
            println!("  --fix              Iteratively apply clippy machine-applicable fixes");
            println!();
            println!("BOOTSTRAP OPTIONS:");
            println!("  --backend=<name>   Backend: llvm, cranelift, c, auto (default: auto)");
            println!("  --output=<dir>     Output directory (default: bootstrap)");
            println!(
                "  --seed=<path>      Seed compiler binary (default: bin/simple or bin/release/<platform>/simple)"
            );
            0
        }
        _ => {
            // For other build subcommands, delegate to the Simple build system via file execution
            let entry = PathBuf::from("src/compiler/80.driver/build/cli_entry.spl");
            if entry.exists() {
                let mut file_args = vec![entry.to_string_lossy().to_string()];
                file_args.extend(sub_args.iter().map(|s| s.to_string()));
                crate::cli::basic::run_file_with_args(&entry, gc_log, gc_off, file_args)
            } else {
                eprintln!("error: unknown build subcommand: {}", cmd);
                1
            }
        }
    }
}

/// Handle 'build lint' - run cargo clippy on the Rust workspace.
///
/// Supports `--fix` to auto-apply clippy machine-applicable suggestions.
/// With `--fix`, runs `cargo clippy --fix` iteratively per crate until the
/// owned-crate warning count stops decreasing. Any residual warnings are
/// non-auto-fixable and require manual review.
fn handle_build_lint() -> i32 {
    handle_build_lint_with_args(&[])
}

fn handle_build_lint_with_args(args: &[&str]) -> i32 {
    let do_fix = args.contains(&"--fix");
    if do_fix {
        return run_clippy_autofix_sweep();
    }
    let status = std::process::Command::new("cargo")
        .args([
            "clippy",
            "--manifest-path",
            "src/compiler_rust/Cargo.toml",
            "--workspace",
            "--",
            "-W",
            "clippy::all",
        ])
        .status();
    match status {
        Ok(s) => s.code().unwrap_or(1),
        Err(e) => {
            eprintln!("error: failed to run cargo clippy: {}", e);
            1
        }
    }
}

/// Run `cargo clippy --fix` iteratively across owned crates until no further
/// auto-fixes apply. Returns 0 on success, non-zero on cargo failure.
///
/// Per cargo design, clippy emits machine-applicable suggestions for many
/// lints (`unnecessary_cast`, `useless_format`, `needless_borrow`,
/// `collapsible_if`, etc.). This sweep applies them workspace-wide; any
/// remaining warnings after the sweep need manual fixes.
fn run_clippy_autofix_sweep() -> i32 {
    println!("=== clippy auto-fix sweep ===");

    // Apply machine-applicable suggestions across the workspace, iterating
    // until the warning count stops going down (some fixes unblock others).
    let mut prev_count: i64 = -1;
    for round in 1..=5 {
        let count = clippy_warning_count();
        println!("round {round}: {count} warnings");
        if count == prev_count || count == 0 {
            println!("=== converged at {count} warnings ===");
            return 0;
        }
        prev_count = count;
        let status = std::process::Command::new("cargo")
            .args([
                "clippy",
                "--manifest-path",
                "src/compiler_rust/Cargo.toml",
                "--workspace",
                "--all-targets",
                "--fix",
                "--allow-dirty",
                "--allow-staged",
                "--",
                "-W",
                "clippy::all",
            ])
            .status();
        match status {
            Ok(s) if s.success() => {}
            Ok(s) => {
                eprintln!("clippy --fix exited with {}", s.code().unwrap_or(1));
                return s.code().unwrap_or(1);
            }
            Err(e) => {
                eprintln!("error: failed to run cargo clippy --fix: {e}");
                return 1;
            }
        }
    }
    let final_count = clippy_warning_count();
    println!("=== max rounds reached; {final_count} warnings remain ===");
    0
}

/// Count `^warning:` lines from `cargo clippy --workspace -W clippy::all`.
/// Excludes per-crate summary lines like `simple-compiler (lib) generated N warnings`.
fn clippy_warning_count() -> i64 {
    let out = std::process::Command::new("cargo")
        .args([
            "clippy",
            "--manifest-path",
            "src/compiler_rust/Cargo.toml",
            "--workspace",
            "--all-targets",
            "--",
            "-W",
            "clippy::all",
        ])
        .output();
    let out = match out {
        Ok(o) => o,
        Err(_) => return -1,
    };
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    combined
        .lines()
        .filter(|l| l.starts_with("warning:") && !l.starts_with("warning: `simple-"))
        .count() as i64
}

/// Handle 'build fmt' - run cargo fmt on the Rust workspace
fn handle_build_fmt(args: &[&str]) -> i32 {
    let mut cmd_args = vec!["fmt", "--manifest-path", "src/compiler_rust/Cargo.toml", "--all"];
    if args.contains(&"--check") {
        cmd_args.push("--check");
    }
    let status = std::process::Command::new("cargo").args(&cmd_args).status();
    match status {
        Ok(s) => s.code().unwrap_or(1),
        Err(e) => {
            eprintln!("error: failed to run cargo fmt: {}", e);
            1
        }
    }
}

/// Handle 'build check' - run lint + fmt check + tests
fn handle_build_check() -> i32 {
    println!("\n=== Running Lint (clippy) ===");
    let lint = handle_build_lint();

    println!("\n=== Running Format Check ===");
    let fmt = handle_build_fmt(&["--check"]);

    println!("\n=== Running Tests ===");
    let test_binary = resolve_preferred_simple_binary()
        .or_else(|| std::env::current_exe().ok())
        .unwrap_or_else(|| PathBuf::from("bin/simple"));
    let test = std::process::Command::new(&test_binary)
        .arg("test")
        .status()
        .map(|s| s.code().unwrap_or(1))
        .unwrap_or(1);

    if lint != 0 {
        lint
    } else if fmt != 0 {
        fmt
    } else {
        test
    }
}

/// Run the 3-stage bootstrap pipeline directly in Rust.
///
/// This is a native implementation of the bootstrap process:
/// Stage 1: Compile compiler with current binary
/// Stage 2: Compile compiler with Stage 1 output
/// Stage 3: Compile compiler with Stage 2 output, verify Stage 2 == Stage 3
fn handle_bootstrap(args: &[&str]) -> i32 {
    use std::process::Command;

    // Check for help
    if args.iter().any(|a| *a == "-h" || *a == "--help") {
        println!("3-stage self-compilation bootstrap pipeline");
        println!();
        println!("USAGE: simple build bootstrap [options]");
        println!();
        println!("OPTIONS:");
        println!("  --backend=<name>   Backend: llvm, cranelift, c, auto (default: auto)");
        println!("  --output=<dir>     Output directory (default: bootstrap)");
        println!("  --no-deploy        Verify only; do not deploy the verified stage");
        println!("  --seed=<path>      Seed compiler binary (default: bin/simple or bin/release/<platform>/simple)");
        println!();
        println!("The seed compiler must be a self-hosted Simple binary capable of");
        println!("running src/app/compile/native.spl to compile the compiler source.");
        return 0;
    }

    // Parse options
    let mut backend = "auto".to_string();
    let mut output_dir = "bootstrap".to_string();
    let mut seed_compiler: Option<String> = None;
    // Deploying the verified stage over a shared path while another lane is
    // using it is unsafe; --no-deploy (or SIMPLE_BOOTSTRAP_NO_DEPLOY=1) makes
    // the run verification-only.
    let mut no_deploy = std::env::var("SIMPLE_BOOTSTRAP_NO_DEPLOY")
        .map(|v| v != "0")
        .unwrap_or(false);
    for arg in args {
        if *arg == "--no-deploy" {
            no_deploy = true;
        }
        if let Some(b) = arg.strip_prefix("--backend=") {
            backend = b.to_string();
        } else if let Some(d) = arg.strip_prefix("--output=") {
            output_dir = d.to_string();
        } else if let Some(s) = arg.strip_prefix("--seed=") {
            seed_compiler = Some(s.to_string());
        }
    }

    println!("Bootstrap pipeline starting...");
    println!("Backend: {}", backend);
    println!("Output dir: {}", output_dir);

    // Ensure output directory exists
    let _ = std::fs::create_dir_all(&output_dir);

    // Find initial compiler.
    // Bootstrap requires a self-hosted Simple compiler that can run native.spl.
    // The Rust driver cannot do this (it uses a Rust-native pipeline).
    // Look for a working compiler in order of preference:
    let compiler = if let Some(seed) = seed_compiler {
        if !PathBuf::from(&seed).exists() {
            eprintln!("Error: seed compiler not found: {}", seed);
            return 1;
        }
        seed
    } else if let Some(path) = resolve_preferred_simple_binary() {
        path.to_string_lossy().to_string()
    } else {
        eprintln!("Error: No compiler binary found at bin/simple or bin/release/<platform>/simple");
        eprintln!("  Use --seed=<path> to specify a self-hosted compiler binary");
        return 1;
    };

    // Pin the input closure BEFORE stage 1, and run all three stages from it.
    // Without this the three stages re-read the live working copy across ~45
    // minutes and can compile different source, making every verdict
    // uninterpretable — see
    // doc/08_tracking/bug/bootstrap_determinism_check_races_live_working_tree_2026-08-21.md
    let repo_root = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let compiler = std::fs::canonicalize(&compiler)
        .map(|p| p.to_string_lossy().to_string())
        .unwrap_or(compiler);
    let abs_output_dir = repo_root.join(&output_dir);
    let snapshot_dir = match std::env::var("SIMPLE_BOOTSTRAP_SNAPSHOT_DIR") {
        Ok(d) => PathBuf::from(d),
        Err(_) => abs_output_dir.join(".input-snapshot"),
    };
    let mut workdir = repo_root.clone();
    let mut snapshot_note = "NOT PINNED (live working copy)".to_string();
    match create_bootstrap_snapshot(&repo_root, &snapshot_dir) {
        Ok(()) => {
            workdir = snapshot_dir.clone();
            snapshot_note = format!("pinned snapshot {}", snapshot_dir.display());
        }
        Err(e) => {
            eprintln!(
                "Warning: could not pin input snapshot at {} ({e}); stages will read the LIVE working copy",
                snapshot_dir.display()
            );
        }
    }
    // The inputs actually fed to the three stages. Re-fingerprinted after stage 3
    // as the safety net: if they moved, the run proves nothing.
    let inputs_before = bootstrap_closure_fingerprint(&workdir.join("src"));
    let inputs_digest = bootstrap_closure_digest(&inputs_before);
    println!(
        "Inputs: {} ({} source files, tree={})",
        snapshot_note,
        inputs_before.len(),
        inputs_digest
    );

    // Stage 1: Compile compiler source with seed compiler.
    // NOTE: every stage compiles to the SAME basename ("simple", in a per-stage
    // subdir) on purpose. native-build embeds the output basename into the
    // binary, so compiling to distinct names (simple_stage1/2/3) made the three
    // outputs differ regardless of codegen determinism — a false MISMATCH that
    // also blocked the VERIFIED->deploy path. Same basename isolates genuine
    // non-determinism from the output filename.
    println!();
    println!("=== Stage 1: Compile with seed compiler ===");
    let stage1_path = bootstrap_stage_output_path(&abs_output_dir.to_string_lossy(), "stage1/simple");
    let stage1 = compile_stage(&compiler, &stage1_path, &backend, &workdir);
    if !stage1.success {
        eprintln!("Stage 1 FAILED");
        return 1;
    }
    println!("Stage 1: OK ({} bytes, hash={})", stage1.size, stage1.hash);

    // Stage 2: Compile again with the SAME seed compiler.
    // The Cranelift-compiled Stage 1 binary cannot yet serve as a compiler
    // (runtime SFFI stubs). For now, re-compile with the seed to verify
    // deterministic output.
    println!();
    println!("=== Stage 2: Compile with seed compiler (determinism check) ===");
    let stage2_path = bootstrap_stage_output_path(&abs_output_dir.to_string_lossy(), "stage2/simple");
    let stage2 = compile_stage(&compiler, &stage2_path, &backend, &workdir);
    if !stage2.success {
        eprintln!("Stage 2 FAILED");
        return 1;
    }
    println!("Stage 2: OK ({} bytes, hash={})", stage2.size, stage2.hash);

    // Stage 3: Third compilation
    println!();
    println!("=== Stage 3: Compile with seed compiler (triple check) ===");
    let stage3_path = bootstrap_stage_output_path(&abs_output_dir.to_string_lossy(), "stage3/simple");
    let stage3 = compile_stage(&compiler, &stage3_path, &backend, &workdir);
    if !stage3.success {
        eprintln!("Stage 3 FAILED");
        return 1;
    }
    println!("Stage 3: OK ({} bytes, hash={})", stage3.size, stage3.hash);

    // Safety net: the three stages prove nothing unless they read the SAME
    // inputs. Re-fingerprint what they actually read; if it moved, the only
    // honest verdict is ERROR (exit 2), never VERIFIED/PARTIAL/MISMATCH.
    println!();
    let inputs_after = bootstrap_closure_fingerprint(&workdir.join("src"));
    if inputs_before.is_empty() {
        println!(
            "ERROR — nothing was checked (no source files found under {}/src)",
            workdir.display()
        );
        return 2;
    }
    if bootstrap_closure_digest(&inputs_after) != inputs_digest {
        let before: std::collections::BTreeMap<&String, &String> = inputs_before.iter().map(|(p, h)| (p, h)).collect();
        let after: std::collections::BTreeMap<&String, &String> = inputs_after.iter().map(|(p, h)| (p, h)).collect();
        let mut changed: Vec<String> = Vec::new();
        for (p, h) in &after {
            match before.get(p) {
                Some(bh) if bh == h => {}
                Some(_) => changed.push((*p).clone()),
                None => changed.push(format!("{} (added)", p)),
            }
        }
        for p in before.keys() {
            if !after.contains_key(*p) {
                changed.push(format!("{} (removed)", p));
            }
        }
        println!(
            "ERROR — inputs changed during the run: {} of {} source file(s) differ: {}",
            changed.len(),
            inputs_before.len(),
            changed.join(", ")
        );
        return 2;
    }

    // Verify
    println!(
        "Inputs stable: {} source file(s), tree={}",
        inputs_before.len(),
        inputs_digest
    );
    println!();
    match classify_bootstrap_verdict(&stage1.hash, &stage2.hash, &stage3.hash) {
        BootstrapVerdict::Verified => {
            println!("Bootstrap VERIFIED: All 3 stages produce identical output");
            println!("  Hash: {}", stage1.hash);
            if no_deploy {
                println!("Deploy skipped (--no-deploy)");
            } else if let Err(e) = deploy_verified_bootstrap_stage(&stage3_path, &output_dir) {
                eprintln!("Bootstrap deploy FAILED: {}", e);
                return 1;
            }
            0
        }
        BootstrapVerdict::Partial => {
            // Deployment requires VERIFIED. The former PARTIAL -> deploy branch
            // was a fail-open; its removal precondition (one VERIFIED run on a
            // pinned snapshot) was met 2026-08-21, so a PARTIAL now can only
            // mean genuine codegen nondeterminism and is never deployed.
            println!(
                "Bootstrap PARTIAL \u{2014} not deployed: stage1 differs (stage1={}, stage2={}, stage3={})",
                stage1.hash, stage2.hash, stage3.hash
            );
            1
        }
        BootstrapVerdict::Mismatch => {
            println!("Bootstrap MISMATCH: outputs differ between stages");
            println!("  Stage 1: {} ({} bytes)", stage1.hash, stage1.size);
            println!("  Stage 2: {} ({} bytes)", stage2.hash, stage2.size);
            println!("  Stage 3: {} ({} bytes)", stage3.hash, stage3.size);
            1
        }
    }
}

/// Verdict for a three-stage bootstrap, decided purely from the stage hashes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BootstrapVerdict {
    /// All three stages produced identical output.
    Verified,
    /// Stage 2 == stage 3 but stage 1 differs (fixpoint reached late).
    Partial,
    /// Anything else.
    Mismatch,
}

/// Classify a bootstrap run from its three stage hashes.
pub fn classify_bootstrap_verdict(s1: &str, s2: &str, s3: &str) -> BootstrapVerdict {
    if s1 == s2 && s2 == s3 {
        BootstrapVerdict::Verified
    } else if s2 == s3 {
        BootstrapVerdict::Partial
    } else {
        BootstrapVerdict::Mismatch
    }
}

#[cfg(test)]
mod bootstrap_verdict_tests {
    use super::{classify_bootstrap_verdict, BootstrapVerdict};

    #[test]
    fn all_equal_is_verified() {
        assert_eq!(classify_bootstrap_verdict("a", "a", "a"), BootstrapVerdict::Verified);
    }

    #[test]
    fn stage1_differs_is_partial() {
        assert_eq!(classify_bootstrap_verdict("a", "b", "b"), BootstrapVerdict::Partial);
    }

    #[test]
    fn stage3_differs_is_mismatch() {
        assert_eq!(classify_bootstrap_verdict("a", "a", "b"), BootstrapVerdict::Mismatch);
        assert_eq!(classify_bootstrap_verdict("a", "b", "c"), BootstrapVerdict::Mismatch);
        assert_eq!(classify_bootstrap_verdict("a", "b", "a"), BootstrapVerdict::Mismatch);
    }
}

/// Source extensions that make up the compiled input closure. Only these are
/// COPIED into the pinned snapshot; every other entry is symlinked back to the
/// live tree (build outputs, `.a`/`.o`, C runtime sources are inputs to the
/// LINK, not to codegen, and copying 16 GB of `src/` is not viable).
const BOOTSTRAP_PINNED_EXTS: [&str; 2] = ["spl", "sdn"];
/// Directories never traversed when building the snapshot; symlinked whole.
const BOOTSTRAP_SNAPSHOT_SKIP_DIRS: [&str; 5] = ["target", "build", "node_modules", ".git", "vendor"];

/// Walk `root` (a `src/` directory), returning (relative path, sha256) for every
/// file in the pinned input closure, sorted by path.
fn bootstrap_closure_fingerprint(root: &Path) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = Vec::new();
    let mut stack: Vec<PathBuf> = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let entries = match std::fs::read_dir(&dir) {
            Ok(e) => e,
            Err(_) => continue,
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let name = entry.file_name().to_string_lossy().to_string();
            let ft = match entry.file_type() {
                Ok(ft) => ft,
                Err(_) => continue,
            };
            if ft.is_symlink() {
                continue;
            }
            if ft.is_dir() {
                if !BOOTSTRAP_SNAPSHOT_SKIP_DIRS.contains(&name.as_str()) {
                    stack.push(path);
                }
            } else if path
                .extension()
                .map(|e| BOOTSTRAP_PINNED_EXTS.contains(&e.to_string_lossy().as_ref()))
                .unwrap_or(false)
            {
                if let Ok(h) = sha256_file(&path.to_string_lossy()) {
                    let rel = path.strip_prefix(root).unwrap_or(&path).to_string_lossy().to_string();
                    out.push((rel, h));
                }
            }
        }
    }
    out.sort();
    out
}

/// Single digest over a closure fingerprint — the snapshot's "tree id".
fn bootstrap_closure_digest(files: &[(String, String)]) -> String {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    for (path, hash) in files {
        hasher.update(path.as_bytes());
        hasher.update(b" ");
        hasher.update(hash.as_bytes());
        hasher.update(b"\n");
    }
    format!("{:x}", hasher.finalize())
}

/// Materialise an immutable snapshot of the input closure at `dest`.
///
/// The working tree is routinely DIRTY (hundreds of uncommitted files across
/// concurrent sessions), so `git worktree add --detach` — the pattern
/// `check-seed-builds-push.shs` uses for the Rust seed — would compile HEAD, i.e.
/// *different* source than the operator asked for. We therefore snapshot the live
/// working-copy CONTENT: source files are copied, everything else is symlinked.
fn create_bootstrap_snapshot(repo_root: &Path, dest: &Path) -> std::io::Result<()> {
    if dest.exists() {
        std::fs::remove_dir_all(dest)?;
    }
    std::fs::create_dir_all(dest)?;

    // Everything at the repo root except `src` is symlinked wholesale: relative
    // paths (bin/, config/, scripts/) keep resolving, and none of it is codegen input.
    for entry in std::fs::read_dir(repo_root)?.flatten() {
        let name = entry.file_name();
        if name == std::ffi::OsStr::new("src") {
            continue;
        }
        let _ = symlink_path(&entry.path(), &dest.join(&name));
    }

    copy_pinned_tree(&repo_root.join("src"), &dest.join("src"))
}

#[cfg(unix)]
fn symlink_path(src: &Path, dst: &Path) -> std::io::Result<()> {
    std::os::unix::fs::symlink(src, dst)
}

#[cfg(not(unix))]
fn symlink_path(src: &Path, dst: &Path) -> std::io::Result<()> {
    if src.is_dir() {
        std::os::windows::fs::symlink_dir(src, dst)
    } else {
        std::os::windows::fs::symlink_file(src, dst)
    }
}

/// Copy the pinned source extensions; symlink every other file and skipped dir.
fn copy_pinned_tree(src: &Path, dst: &Path) -> std::io::Result<()> {
    std::fs::create_dir_all(dst)?;
    for entry in std::fs::read_dir(src)?.flatten() {
        let path = entry.path();
        let name = entry.file_name();
        let target = dst.join(&name);
        let ft = match entry.file_type() {
            Ok(ft) => ft,
            Err(_) => continue,
        };
        if ft.is_symlink() {
            // Preserve RELATIVE link targets verbatim so they keep resolving
            // INSIDE the snapshot. Pointing them back at the live tree is an
            // escape: `src/std -> lib` is a stdlib root candidate, so a
            // live-pointing `src/std` hands every stage the live `src/lib`
            // regardless of the copy — the exact race this snapshot exists to
            // close. Absolute targets are reproduced as-is.
            match std::fs::read_link(&path) {
                Ok(link_target) if link_target.is_relative() => {
                    let _ = symlink_path(&link_target, &target);
                }
                _ => {
                    let _ = symlink_path(&path, &target);
                }
            }
        } else if ft.is_dir() {
            if BOOTSTRAP_SNAPSHOT_SKIP_DIRS.contains(&name.to_string_lossy().as_ref()) {
                let _ = symlink_path(&path, &target);
            } else {
                copy_pinned_tree(&path, &target)?;
            }
        } else if path
            .extension()
            .map(|e| BOOTSTRAP_PINNED_EXTS.contains(&e.to_string_lossy().as_ref()))
            .unwrap_or(false)
        {
            std::fs::copy(&path, &target)?;
        } else {
            let _ = symlink_path(&path, &target);
        }
    }
    Ok(())
}

fn bootstrap_stage_output_path(output_dir: &str, name: &str) -> String {
    let mut path = PathBuf::from(output_dir).join(name);
    if cfg!(target_os = "windows") && path.extension().is_none() {
        path.set_extension("exe");
    }
    // `name` may include a per-stage subdir (e.g. "stage1/simple"); ensure it exists.
    if let Some(parent) = path.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    path.to_string_lossy().to_string()
}

struct StageResult {
    success: bool,
    size: u64,
    hash: String,
}

/// Native-build worker count for a bootstrap stage.
///
/// `SIMPLE_BOOTSTRAP_THREADS=<n>` overrides (n=1 restores the old serial
/// behaviour); otherwise half the host CPUs, capped at 8. The cap is a MEMORY
/// bound, not a determinism one: each LLVM worker owns a full
/// `inkwell::Context` + optimizer and peaks GB-scale, which is why
/// `resolve_num_threads` (`compiler/src/pipeline/native_project/mod.rs`,
/// `LLVM_DEFAULT_MAX_THREADS`) clamps LLVM parallelism at all.
///
/// Output is thread-count independent: modules compile to separate objects and
/// link in a fixed order. Verified 2026-08-21 on a 7-module pinned input with
/// per-run private cache scopes (so every run really compiled: "7 compiled, 0
/// cached") — --threads 1 x2 and --threads 8 x2 all produced sha256
/// 41c5b4d4df287797ffb7bdd821808a1c...
fn bootstrap_threads() -> usize {
    if let Ok(n) = std::env::var("SIMPLE_BOOTSTRAP_THREADS") {
        if let Ok(n) = n.parse::<usize>() {
            if n > 0 {
                return n;
            }
        }
    }
    let cores = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
    (cores / 2).clamp(1, 8)
}

/// Compile one bootstrap stage.
///
/// `workdir` is the directory the compiler is run FROM. All three stages must be
/// given the SAME pinned snapshot directory, otherwise they read the live working
/// copy and can compile different source — see
/// `doc/08_tracking/bug/bootstrap_determinism_check_races_live_working_tree_2026-08-21.md`.
/// `compiler` and `output` must therefore be absolute paths.
fn compile_stage(compiler: &str, output: &str, backend: &str, workdir: &Path) -> StageResult {
    use std::process::Command;

    // Rust driver uses native-build with --entry-closure for cross-module resolution:
    //   compiler native-build --source ... --entry ... --entry-closure -o <output>
    // Self-hosted Simple format:
    //   compiler src/app/compile/native.spl src/app/cli/main.spl <output>
    // Path-based classification alone is not enough: the Rust seed is routinely
    // deployed to bin/release/<triple>/simple (a path that normally holds the
    // self-hosted binary). Misclassifying it as self-hosted sends
    // `--backend=llvm-lib`, which the seed's dispatch routes to the INTERPRETED
    // native_build_main.spl worker — a pathological path that loads the whole
    // compiler import graph under the tree-walking interpreter (observed
    // 2026-08-18: 28.4 GB RSS, killed after 5508s, no binary). Probe the actual
    // binary: the seed's --version prints a "bootstrap seed" warning banner.
    let is_rust_driver = is_rust_driver_binary(compiler) || binary_reports_rust_seed(compiler);

    let mut cmd = Command::new(compiler);
    cmd.current_dir(workdir);
    cmd.env_remove("_SIMPLE_STACK_SET");
    if is_rust_driver {
        // Force the seed's in-process native_project pipeline. Without this the
        // seed's own dispatch treats native-build as a pure-Simple tool and
        // interprets src/app/cli/native_build_main.spl, which spawns the
        // interpreted worker — the same pathological path described above.
        cmd.env("SIMPLE_NATIVE_BUILD_RUST", "1");
        cmd.arg("native-build")
            .arg("--source")
            .arg("src/app")
            .arg("--entry")
            .arg("src/app/cli/bootstrap_main.spl")
            .arg("--entry-closure")
            .arg("--strip")
            .arg("--threads")
            .arg(bootstrap_threads().to_string())
            .arg("--timeout")
            .arg("180")
            .arg("-o")
            .arg(output);
        cmd.env("SIMPLE_BOOTSTRAP", "1");
        cmd.env("SIMPLE_NO_STUB_FALLBACK", "1");
        if let Ok(rtp) = std::env::var("SIMPLE_RUNTIME_PATH") {
            cmd.env("SIMPLE_RUNTIME_PATH", rtp);
        }
        println!(
            "  Running: {} native-build --source src/app --entry-closure --strip --threads {} --timeout 180 --entry src/app/cli/bootstrap_main.spl -o {}",
            compiler, bootstrap_threads(), output
        );
    } else {
        cmd.arg("native-build")
            .arg("--source")
            .arg("src/app")
            .arg("--entry")
            .arg("src/app/cli/bootstrap_main.spl")
            .arg("--entry-closure")
            .arg("--strip")
            .arg("--threads")
            .arg(bootstrap_threads().to_string())
            .arg("--timeout")
            .arg("180")
            .arg("-o")
            .arg(output);
        // The self-hosted native-build lane only accepts the pure-Simple LLVM
        // backend (`llvm-lib`); `auto`/`llvm` must be normalized to it or the
        // receiver's dispatch (src/app/cli/_CliMain) rejects the invocation with
        // "native-build requires --backend=llvm-lib in the pure Simple command path".
        // `auto` must never resolve to a backend the seed cannot actually run:
        // a seed linked against a libsimple_native_all.a built without the
        // 'llvm' cargo feature fails every file with "'llvm' feature not
        // enabled". Probe the seed once and fall back to cranelift.
        let sh_backend = match backend {
            "llvm" | "llvm-lib" | "llvmlib" => "llvm-lib",
            "auto" => {
                if seed_supports_llvm(compiler) {
                    "llvm-lib"
                } else {
                    println!(
                        "  Backend auto: seed cannot use llvm (built without the 'llvm' feature) — using cranelift"
                    );
                    "cranelift"
                }
            }
            other => other,
        };
        cmd.arg(format!("--backend={}", sh_backend));
        println!(
            "  Running: {} native-build --source src/app --entry-closure --strip --threads {} --timeout 180 --entry src/app/cli/bootstrap_main.spl -o {} --backend={}",
            compiler, bootstrap_threads(), output, sh_backend
        );
    }

    // Use inherited stdio so the user can see progress
    let status = cmd.stdin(std::process::Stdio::null()).status();

    match status {
        Ok(exit_status) => {
            if !exit_status.success() {
                eprintln!("  Compile failed (exit {:?})", exit_status.code());
                if let Some(code) = exit_status.code() {
                    if code == 139 {
                        eprintln!("[LIM-010] SEGFAULT (exit 139) — likely LLVM constructor conflict");
                        eprintln!("[LIM-010] Ensure objcopy is available and strip_llvm_constructors() succeeded");
                    }
                }
                return StageResult {
                    success: false,
                    size: 0,
                    hash: String::new(),
                };
            }

            // Get file size
            let size = std::fs::metadata(output).map(|m| m.len()).unwrap_or(0);

            let hash = sha256_file(output).unwrap_or_else(|e| {
                eprintln!("  Failed to hash output: {e}");
                String::new()
            });

            StageResult {
                success: true,
                size,
                hash,
            }
        }
        Err(e) => {
            eprintln!("  Failed to execute compiler: {}", e);
            StageResult {
                success: false,
                size: 0,
                hash: String::new(),
            }
        }
    }
}

fn deploy_verified_bootstrap_stage(stage3_path: &str, output_dir: &str) -> Result<(), String> {
    let deploy_path = bootstrap_stage3_deploy_path(output_dir);
    if let Some(parent) = deploy_path.parent() {
        std::fs::create_dir_all(parent).map_err(|e| format!("create {}: {e}", parent.display()))?;
    }
    std::fs::copy(stage3_path, &deploy_path)
        .map_err(|e| format!("copy {stage3_path} -> {}: {e}", deploy_path.display()))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = std::fs::metadata(&deploy_path)
            .map_err(|e| format!("stat {}: {e}", deploy_path.display()))?
            .permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(&deploy_path, perms).map_err(|e| format!("chmod {}: {e}", deploy_path.display()))?;
    }
    println!("Bootstrap deployed: {}", deploy_path.display());
    Ok(())
}

fn bootstrap_stage3_deploy_path(output_dir: &str) -> PathBuf {
    let triple = if cfg!(target_os = "linux") && cfg!(target_arch = "x86_64") {
        "x86_64-unknown-linux-gnu"
    } else if cfg!(target_os = "linux") && cfg!(target_arch = "aarch64") {
        "aarch64-unknown-linux-gnu"
    } else if cfg!(target_os = "macos") && cfg!(target_arch = "aarch64") {
        "aarch64-apple-darwin-macho"
    } else if cfg!(target_os = "macos") && cfg!(target_arch = "x86_64") {
        "x86_64-apple-darwin-macho"
    } else if cfg!(target_os = "freebsd") && cfg!(target_arch = "x86_64") {
        "x86_64-unknown-freebsd"
    } else {
        "unknown-host"
    };
    let mut path = PathBuf::from(output_dir).join("stage3").join(triple).join("simple");
    if cfg!(target_os = "windows") {
        path.set_extension("exe");
    }
    path
}

fn sha256_file(path: &str) -> Result<String, String> {
    use sha2::{Digest, Sha256};
    use std::io::Read;

    let mut file = std::fs::File::open(path).map_err(|e| format!("open {path}: {e}"))?;
    let mut hasher = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let n = file.read(&mut buffer).map_err(|e| format!("read {path}: {e}"))?;
        if n == 0 {
            break;
        }
        hasher.update(&buffer[..n]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

fn resolve_preferred_simple_binary() -> Option<PathBuf> {
    let mut candidates = vec![
        PathBuf::from("build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple"),
        PathBuf::from("build/bootstrap/stage3/aarch64-unknown-linux-gnu/simple"),
        PathBuf::from("build/bootstrap/full/x86_64-unknown-linux-gnu/simple"),
        PathBuf::from("build/bootstrap/full/aarch64-unknown-linux-gnu/simple"),
        PathBuf::from("build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple"),
        PathBuf::from("build/bootstrap/stage2/aarch64-unknown-linux-gnu/simple"),
        PathBuf::from("build/bootstrap/stage2_fullcli/simple"),
    ];
    // Prefer real host-platform binaries (bin/release/<triple>/simple) next.
    // They run on the host AND are not misclassified as rust-driver seeds — a
    // rust-driver seed (e.g. the `bin/simple` symlink) sets
    // SIMPLE_NO_STUB_FALLBACK=1, which breaks the minimal bootstrap entry that
    // legitimately needs libc stubs. No Linux regression: whenever the generic
    // wrapper worked, the platform binary it execs exists and is found here.
    candidates.extend(platform_release_binary_candidates());
    candidates.extend([
        PathBuf::from("bin/simple"),
        PathBuf::from("src/compiler_rust/target/release/simple"),
        PathBuf::from("src/compiler_rust/target/bootstrap/simple"),
        // Generic wrapper: may exec a binary for the wrong platform
        // (e.g. a Linux wrapper on macOS -> "Exec format error"). Last resort.
        PathBuf::from("bin/release/simple"),
    ]);

    candidates.into_iter().find(|candidate| candidate.is_file())
}

fn platform_release_binary_candidates() -> Vec<PathBuf> {
    let mut candidates = Vec::new();

    if cfg!(target_os = "windows") {
        if cfg!(target_arch = "x86_64") {
            candidates.push(PathBuf::from("bin/release/x86_64-pc-windows-msvc/simple.exe"));
            candidates.push(PathBuf::from("bin/release/x86_64-pc-windows-gnu/simple.exe"));
        }
        if cfg!(target_arch = "aarch64") {
            candidates.push(PathBuf::from("bin/release/aarch64-pc-windows-msvc/simple.exe"));
            candidates.push(PathBuf::from("bin/release/aarch64-pc-windows-gnu/simple.exe"));
        }
    } else if cfg!(target_os = "macos") {
        if cfg!(target_arch = "aarch64") {
            candidates.push(PathBuf::from("bin/release/aarch64-apple-darwin-macho/simple"));
            candidates.push(PathBuf::from("bin/release/macos-arm64/simple"));
            candidates.push(PathBuf::from("bin/release/darwin-aarch64/simple"));
        }
        if cfg!(target_arch = "x86_64") {
            candidates.push(PathBuf::from("bin/release/macos-x86_64/simple"));
            candidates.push(PathBuf::from("bin/release/darwin-x86_64/simple"));
        }
    } else if cfg!(target_os = "linux") {
        if cfg!(target_arch = "x86_64") {
            candidates.push(PathBuf::from("bin/release/linux-x86_64/simple"));
            candidates.push(PathBuf::from("bin/release/x86_64-unknown-linux-gnu/simple"));
        }
        if cfg!(target_arch = "aarch64") {
            candidates.push(PathBuf::from("bin/release/linux-aarch64/simple"));
            candidates.push(PathBuf::from("bin/release/aarch64-unknown-linux-gnu/simple"));
        }
    }

    candidates
}

/// True when `compiler` is actually the Rust bootstrap seed, regardless of the
/// path it was deployed to. The seed prints a distinctive warning banner on
/// `--version` ("bootstrap seed"); a genuine self-hosted binary does not, so
/// this probe is behavior-neutral when a healthy self-hosted binary exists.
/// Cheap (~20ms) and fail-open: any spawn/parse failure returns false, leaving
/// classification to the path-based check.
fn binary_reports_rust_seed(compiler: &str) -> bool {
    std::process::Command::new(compiler)
        .arg("--version")
        // The banner is suppressed by SIMPLE_RUST_SEED_WARNING=0 or
        // SIMPLE_BOOTSTRAP=1; strip both so the probe always sees it on a seed.
        .env_remove("SIMPLE_RUST_SEED_WARNING")
        .env_remove("SIMPLE_BOOTSTRAP")
        .output()
        .map(|out| {
            let text = format!(
                "{}{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
            text.contains("bootstrap seed")
        })
        .unwrap_or(false)
}

/// Probe whether a self-hosted seed can actually codegen through llvm.
///
/// The pure-Simple `native-build` lane routes `llvm-lib` into the linked
/// `rt_native_build` pipeline; when that static library was built without the
/// 'llvm' cargo feature every file fails. One tiny compile answers it. Cached:
/// the bootstrap runs three stages with the same seed.
fn seed_supports_llvm(compiler: &str) -> bool {
    use std::sync::OnceLock;
    static CACHE: OnceLock<bool> = OnceLock::new();
    *CACHE.get_or_init(|| {
        let dir = std::env::temp_dir().join(format!("simple-llvm-probe-{}", std::process::id()));
        if std::fs::create_dir_all(&dir).is_err() {
            return true;
        }
        let src = dir.join("probe.spl");
        if std::fs::write(&src, "fn main():\n    print \"probe\"\n").is_err() {
            return true;
        }
        let out = std::process::Command::new(compiler)
            .arg("native-build")
            .arg("--source")
            .arg(&dir)
            .arg("--entry")
            .arg(&src)
            .arg("--entry-closure")
            .arg("--backend=llvm-lib")
            .arg("-o")
            .arg(dir.join("probe"))
            .stdin(std::process::Stdio::null())
            .output();
        let supported = match out {
            Ok(out) => {
                let text = format!(
                    "{}{}",
                    String::from_utf8_lossy(&out.stdout),
                    String::from_utf8_lossy(&out.stderr)
                );
                !text.contains("'llvm' feature not enabled") && !text.contains("without the 'llvm' cargo feature")
            }
            // Could not run the probe: don't silently downgrade the backend.
            Err(_) => true,
        };
        let _ = std::fs::remove_dir_all(&dir);
        supported
    })
}

fn is_rust_driver_binary(compiler: &str) -> bool {
    let normalized = compiler.replace('\\', "/");
    normalized == "src/compiler_rust/target/release/simple"
        || normalized == "src/compiler_rust/target/release/simple.exe"
        || normalized.ends_with("/src/compiler_rust/target/release/simple")
        || normalized.ends_with("/src/compiler_rust/target/release/simple.exe")
        || normalized == "src/compiler_rust/target/bootstrap/simple"
        || normalized == "src/compiler_rust/target/bootstrap/simple.exe"
        || normalized.ends_with("/src/compiler_rust/target/bootstrap/simple")
        || normalized.ends_with("/src/compiler_rust/target/bootstrap/simple.exe")
        || normalized == "bin/simple"
        || normalized == "bin/simple.exe"
        || normalized.ends_with("/bin/simple")
        || normalized.ends_with("/bin/simple.exe")
        || normalized.contains("/bin/release/")
        || normalized.ends_with("/target/bootstrap/simple")
        || normalized.ends_with("/target/bootstrap/simple.exe")
        || normalized.ends_with("/target/release/simple")
        || normalized.ends_with("/target/release/simple.exe")
        || normalized.ends_with("/target/debug/simple")
        || normalized.ends_with("/target/debug/simple.exe")
        || normalized == "simple"
        || normalized == "simple.exe"
}

/// Handle 'brief' command - LLM-friendly code overview
pub fn handle_brief(args: &[String], gc_log: bool, gc_off: bool) -> i32 {
    // Skip the command name ("brief") and pass remaining args
    let brief_args: Vec<String> = args[1..]
        .iter()
        .map(|a| format!("\"{}\"", a.replace("\"", "\\\"")))
        .collect();

    let code = format!(
        r#"use tooling.brief_view.{{run_brief}}

fn main() -> i64:
    val args = [{}]
    run_brief(args) as i64"#,
        brief_args.join(", ")
    );

    crate::cli::basic::run_code(&code, gc_log, gc_off)
}

/// Handle 'check-skip' command - scan test files for skip/pending markers
pub fn handle_check_skip(args: &[String]) -> i32 {
    let entry = std::path::PathBuf::from("src/app/check_skip/main.spl");
    if entry.exists() {
        let mut file_args = vec![entry.to_string_lossy().to_string()];
        file_args.extend(args[1..].iter().cloned());
        crate::cli::basic::run_file_with_args(&entry, false, false, file_args)
    } else {
        eprintln!("error: check-skip requires Simple implementation at src/app/check_skip/main.spl");
        1
    }
}

/// Handle 'dashboard' command - project dashboard CLI
pub fn handle_dashboard(args: &[String], _gc_log: bool, _gc_off: bool) -> i32 {
    let dashboard_args: Vec<String> = if args.len() > 1 {
        args[1..]
            .iter()
            .map(|a| format!("\"{}\"", a.replace("\"", "\\\"")))
            .collect()
    } else {
        vec![]
    };

    let code = format!(
        r#"use app.dashboard.main.{{run_dashboard}}

fn main() -> i64:
    val args = [{}]
    run_dashboard(args)"#,
        dashboard_args.join(", ")
    );

    crate::cli::basic::run_code(&code, false, false)
}

#[cfg(test)]
mod bootstrap_determinism_tests {
    //! Reproduce checks for
    //! `doc/08_tracking/bug/bootstrap_determinism_check_races_live_working_tree_2026-08-21.md`.
    //!
    //! The gate asserted "deterministic output" while re-reading a MUTABLE input
    //! on each of three ~15-minute trials, so its control (identical input) was
    //! never held: a MISMATCH could mean nondeterministic codegen or an edit
    //! landing mid-run, and the two are indistinguishable. These tests pin the
    //! race detector that makes the verdict interpretable — it is the piece
    //! whose silent removal would restore the fail-open without any other
    //! visible change.
    use super::{bootstrap_closure_digest, bootstrap_closure_fingerprint};
    use std::path::{Path, PathBuf};

    fn scratch(tag: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "bootstrap-determinism-{}-{}-{:?}",
            tag,
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("compiler")).unwrap();
        std::fs::write(dir.join("app.spl"), "fn main():\n    print \"a\"\n").unwrap();
        std::fs::write(dir.join("compiler/mono.spl"), "fn lower():\n    0\n").unwrap();
        std::fs::write(dir.join("compiler/reg.sdn"), "name: reg\n").unwrap();
        dir
    }

    fn digest_of(root: &Path) -> String {
        bootstrap_closure_digest(&bootstrap_closure_fingerprint(root))
    }

    #[test]
    fn fingerprint_is_stable_when_the_tree_does_not_move() {
        let dir = scratch("stable");
        assert_eq!(
            digest_of(&dir),
            digest_of(&dir),
            "a tree that did not change must fingerprint identically; \
             otherwise the race detector would cry wolf on every run"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn fingerprint_moves_when_a_closure_source_is_edited_mid_run() {
        // The incident's exact shape: files under src/compiler/40.mono and
        // 50.mir were edited BETWEEN the stage1 and stage2 artifacts.
        let dir = scratch("edited");
        let before = digest_of(&dir);
        std::fs::write(dir.join("compiler/mono.spl"), "fn lower():\n    1\n").unwrap();
        let after = digest_of(&dir);
        assert_ne!(
            before, after,
            "an edit to a closure source between two stages MUST be detectable; \
             this is what turns an uninterpretable MISMATCH/PARTIAL into \
             'ERROR — inputs changed during the run'"
        );

        let fp_before = bootstrap_closure_fingerprint(&dir);
        std::fs::write(dir.join("compiler/mono.spl"), "fn lower():\n    0\n").unwrap();
        let fp_restored = bootstrap_closure_fingerprint(&dir);
        assert_eq!(
            fp_restored.len(),
            fp_before.len(),
            "restoring content must not change the file set"
        );
        assert_eq!(
            digest_of(&dir),
            before,
            "the digest is content-addressed, not order- or time-dependent"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn a_new_closure_file_moves_the_fingerprint() {
        let dir = scratch("added");
        let before = digest_of(&dir);
        std::fs::write(dir.join("compiler/added.spl"), "fn extra():\n    0\n").unwrap();
        assert_ne!(
            before,
            digest_of(&dir),
            "a source file appearing mid-run changes the compiled closure and \
             must be caught, not just an edit to an existing one"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn non_closure_files_do_not_move_the_fingerprint() {
        // Build outputs and C sources are inputs to the LINK, not to codegen,
        // and churn constantly. If they counted, the detector would be
        // permanently red and would get routed around.
        let dir = scratch("noise");
        let before = digest_of(&dir);
        std::fs::write(dir.join("compiler/obj.o"), "not source").unwrap();
        std::fs::write(dir.join("compiler/runtime.c"), "int main(void){return 0;}").unwrap();
        std::fs::create_dir_all(dir.join("target")).unwrap();
        std::fs::write(dir.join("target/generated.spl"), "fn gen():\n    0\n").unwrap();
        assert_eq!(
            before,
            digest_of(&dir),
            "only .spl/.sdn outside the skipped directories are the pinned closure"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn an_empty_closure_fingerprints_to_nothing_so_the_caller_must_error() {
        // Non-vacuity: the caller emits `ERROR — nothing was checked` on an
        // empty closure. A fingerprint that quietly returned a stable digest
        // for an empty tree would make that branch unreachable and let a
        // bootstrap over zero source files report VERIFIED.
        let dir = std::env::temp_dir().join(format!("bootstrap-determinism-empty-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        assert!(
            bootstrap_closure_fingerprint(&dir).is_empty(),
            "an empty closure must fingerprint to zero files"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }
}
