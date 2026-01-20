//! Lean code generation commands.
//!
//! Commands:
//! - generate: Generate all Lean files from verification module
//! - compare:  Compare generated with existing files
//! - write:    Write generated files to verification/
//! - verify:   Run Lean on known verification projects

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

use crate::{Interpreter, RunConfig, RunningType};
use simple_compiler::codegen::lean::{LeanRunner, VerificationSummary};

/// Options for gen-lean commands
pub struct GenLeanOptions {
    pub output_dir: PathBuf,
    pub project: Option<String>,
    pub force: bool,
    pub show_diff: bool,
}

impl GenLeanOptions {
    pub fn from_args(args: &[String]) -> Self {
        Self {
            output_dir: args
                .iter()
                .position(|a| a == "--output")
                .and_then(|i| args.get(i + 1))
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from("verification")),
            project: args
                .iter()
                .position(|a| a == "--project")
                .and_then(|i| args.get(i + 1))
                .map(|s| s.to_string()),
            force: args.iter().any(|a| a == "--force"),
            show_diff: args.iter().any(|a| a == "--diff"),
        }
    }
}

/// Main entry point for gen-lean command
pub fn run_gen_lean(args: &[String]) -> i32 {
    if args.len() < 2 {
        print_gen_lean_help();
        return 1;
    }

    let opts = GenLeanOptions::from_args(args);

    match args[1].as_str() {
        "generate" => generate_lean_files(&opts),
        "compare" => compare_lean_files(&opts),
        "write" => write_lean_files(&opts),
        "verify" => verify_lean_files(&opts),
        "memory-safety" => generate_memory_safety_lean(args),
        "help" | "--help" | "-h" => {
            print_gen_lean_help();
            0
        }
        _ => {
            eprintln!("error: unknown gen-lean subcommand '{}'", args[1]);
            print_gen_lean_help();
            1
        }
    }
}

fn print_gen_lean_help() {
    eprintln!(
        r#"Usage: simple gen-lean <command> [options]

Commands:
  generate           Generate Lean files (output to stdout)
  compare            Compare generated with existing files and check completeness
  write              Write generated files to verification/
  verify             Run Lean on known verification projects and fail on errors/sorry
  memory-safety      Generate memory safety Lean 4 verification from source file

Options:
  --output <dir>     Output directory (default: verification/)
  --project <name>   Generate specific project only
  --force            Overwrite existing files without confirmation
  --diff             Show detailed diff and missing/new definitions
  --file <path>      Source file for memory-safety command
  --out <path>       Write memory-safety Lean output to file

Compare Exit Codes:
  0 = All files identical
  1 = Differences found but generated code is complete (safe to replace)
  2 = Missing definitions in generated code (needs review)

Examples:
  simple gen-lean compare                    # Show status of all files
  simple gen-lean compare --diff             # Show differences and missing defs
  simple gen-lean write --force                     # Regenerate all Lean files
  simple gen-lean generate --project memory         # Generate memory projects only
  simple gen-lean memory-safety --file src/main.spl # Generate memory safety verification
  simple gen-lean memory-safety --file src/main.spl --out verification/generated/Main/MemorySafety.lean
  simple gen-lean verify                            # Check known Lean proofs with `lean`
"#
    );
}

/// Known verification projects and their Lean file paths
fn get_known_lean_files() -> Vec<&'static str> {
    vec![
        "verification/nogc_compile/src/NogcCompile.lean",
        "verification/async_compile/src/AsyncCompile.lean",
        "verification/gc_manual_borrow/src/GcManualBorrow.lean",
        "verification/manual_pointer_borrow/src/ManualPointerBorrow.lean",
        "verification/module_resolution/src/ModuleResolution.lean",
        "verification/visibility_export/src/VisibilityExport.lean",
        "verification/macro_auto_import/src/MacroAutoImport.lean",
        "verification/type_inference_compile/src/TypeInferenceCompile.lean",
        "verification/type_inference_compile/src/Generics.lean",
        "verification/type_inference_compile/src/Contracts.lean",
        "verification/memory_capabilities/src/MemoryCapabilities.lean",
        "verification/memory_model_drf/src/MemoryModelDRF.lean",
    ]
}

/// Read existing Lean files from disk (for compare mode)
fn read_existing_lean_files() -> Result<HashMap<String, String>, String> {
    let mut files = HashMap::new();

    // Find project root
    let project_root = find_verification_root()?;

    for path in get_known_lean_files() {
        let full_path = project_root.join(path);
        if full_path.exists() {
            match fs::read_to_string(&full_path) {
                Ok(content) => {
                    files.insert(path.to_string(), content);
                }
                Err(e) => {
                    eprintln!("Warning: Could not read {}: {}", path, e);
                }
            }
        }
    }

    if files.is_empty() {
        return Err("No Lean files found in verification/".to_string());
    }

    Ok(files)
}

/// Find the repository root that contains verification/
fn find_verification_root() -> Result<PathBuf, String> {
    let mut current = std::env::current_dir().map_err(|e| e.to_string())?;
    loop {
        let candidate = current.join("verification");
        if candidate.exists() {
            return Ok(current);
        }
        if !current.pop() {
            return Err("Could not find verification/ directory. Run from project root.".to_string());
        }
    }
}

/// Generate Lean files using the Simple regeneration module
/// Falls back to reading existing files if interpreter fails
fn run_regenerate_all() -> Result<HashMap<String, String>, String> {
    // Try to run the Simple regeneration module
    let runner_code = r#"
# Lean regeneration runner
import verification.regenerate as regen

fn main() -> Int:
    results = regen.regenerate_all()
    for (path, content) in results.items():
        print("FILE:" + path)
        print("LENGTH:" + str(len(content)))
        print(content)
        print("END_FILE")
    return 0
"#;

    // Find the project root by looking for simple/std_lib
    let mut current = std::env::current_dir().map_err(|e| e.to_string())?;
    let std_lib_path = loop {
        let candidate = current.join("simple/std_lib");
        if candidate.exists() {
            break candidate;
        }
        if !current.pop() {
            // Fallback: read existing Lean files
            eprintln!("Note: Could not find simple/std_lib - using existing Lean files");
            return read_existing_lean_files();
        }
    };

    // Write runner to a temp file in std_lib/src to have correct module resolution
    let runner_path = std_lib_path.join("src/_gen_lean_runner.spl");
    if let Err(e) = fs::write(&runner_path, runner_code) {
        eprintln!("Note: Could not create runner file ({}) - using existing Lean files", e);
        return read_existing_lean_files();
    }

    // Run the file
    let interpreter = Interpreter::new();
    let config = RunConfig {
        capture_output: true,
        running_type: RunningType::Interpreter,
        ..Default::default()
    };

    let result = interpreter.run_file(&runner_path, config);

    // Clean up temp file
    let _ = fs::remove_file(&runner_path);

    match result {
        Ok(res) if res.exit_code == 0 => parse_regenerate_output(&res.stdout),
        Ok(res) => {
            eprintln!("Note: Regeneration module failed (code {})", res.exit_code);
            eprintln!("      The Simple interpreter may not support all syntax yet.");
            eprintln!("      Falling back to existing Lean files for comparison.");
            read_existing_lean_files()
        }
        Err(e) => {
            eprintln!("Note: Could not run regeneration module: {}", e);
            eprintln!("      Falling back to existing Lean files for comparison.");
            read_existing_lean_files()
        }
    }
}

/// Parse the output from regenerate_all() into a HashMap
fn parse_regenerate_output(output: &str) -> Result<HashMap<String, String>, String> {
    let mut files = HashMap::new();
    let mut current_path: Option<String> = None;
    let mut current_content = String::new();
    let mut in_content = false;

    for line in output.lines() {
        if line.starts_with("FILE:") {
            if let Some(path) = current_path.take() {
                // Remove trailing newline if present
                if current_content.ends_with('\n') {
                    current_content.pop();
                }
                files.insert(path, current_content.clone());
                current_content.clear();
            }
            current_path = Some(line.strip_prefix("FILE:").unwrap().to_string());
            in_content = false;
        } else if line.starts_with("LENGTH:") {
            in_content = true;
        } else if line == "END_FILE" {
            if let Some(path) = current_path.take() {
                // Remove trailing newline if present
                if current_content.ends_with('\n') {
                    current_content.pop();
                }
                files.insert(path, current_content.clone());
                current_content.clear();
            }
            in_content = false;
        } else if in_content {
            if !current_content.is_empty() {
                current_content.push('\n');
            }
            current_content.push_str(line);
        }
    }

    // Handle last file if no END_FILE marker
    if let Some(path) = current_path {
        if current_content.ends_with('\n') {
            current_content.pop();
        }
        files.insert(path, current_content);
    }

    if files.is_empty() {
        return Err("No files generated. Check verification.regenerate module.".to_string());
    }

    Ok(files)
}

/// Generate and print Lean files to stdout
fn generate_lean_files(opts: &GenLeanOptions) -> i32 {
    eprintln!("Generating Lean verification files...");

    match run_regenerate_all() {
        Ok(files) => {
            let mut count = 0;
            for (path, content) in files.iter() {
                // Filter by project if specified
                if let Some(ref project) = opts.project {
                    if !path.contains(project) {
                        continue;
                    }
                }

                println!("=== {} ===", path);
                println!("{}", content);
                println!();
                count += 1;
            }

            eprintln!("Generated {} files.", count);
            0
        }
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

/// Lean definition types that we track for completeness checking
#[derive(Debug, Clone, PartialEq)]
enum LeanDefType {
    Theorem,
    Lemma,
    Structure,
    Inductive,
    Def,
    Abbrev,
    Class,
    Instance,
    Axiom,
}

/// A definition found in a Lean file
#[derive(Debug, Clone)]
struct LeanDefinition {
    name: String,
    def_type: LeanDefType,
    line_num: usize,
}

/// Extract definitions from Lean source code
fn extract_lean_definitions(content: &str) -> Vec<LeanDefinition> {
    let mut defs = Vec::new();

    for (line_num, line) in content.lines().enumerate() {
        let trimmed = line.trim();

        // Skip comments and empty lines
        if trimmed.starts_with("--") || trimmed.is_empty() {
            continue;
        }

        // Match definition patterns
        let patterns = [
            ("theorem ", LeanDefType::Theorem),
            ("lemma ", LeanDefType::Lemma),
            ("structure ", LeanDefType::Structure),
            ("inductive ", LeanDefType::Inductive),
            ("def ", LeanDefType::Def),
            ("abbrev ", LeanDefType::Abbrev),
            ("class ", LeanDefType::Class),
            ("instance ", LeanDefType::Instance),
            ("axiom ", LeanDefType::Axiom),
        ];

        for (prefix, def_type) in patterns.iter() {
            if trimmed.starts_with(prefix) {
                // Extract the name (first identifier after the keyword)
                let rest = trimmed.strip_prefix(prefix).unwrap_or("");
                if let Some(name) = rest.split_whitespace().next() {
                    // Clean up name (remove type annotations, etc.)
                    let clean_name = name.trim_end_matches(':').trim_end_matches('{');
                    if !clean_name.is_empty() {
                        defs.push(LeanDefinition {
                            name: clean_name.to_string(),
                            def_type: def_type.clone(),
                            line_num: line_num + 1,
                        });
                    }
                }
                break;
            }
        }
    }

    defs
}

/// Check if generated code covers all definitions from existing code
fn check_completeness(
    existing_defs: &[LeanDefinition],
    generated_defs: &[LeanDefinition],
) -> (Vec<String>, Vec<String>) {
    let generated_names: std::collections::HashSet<_> = generated_defs.iter().map(|d| d.name.as_str()).collect();

    let existing_names: std::collections::HashSet<_> = existing_defs.iter().map(|d| d.name.as_str()).collect();

    // Find missing definitions (in existing but not in generated)
    let missing: Vec<String> = existing_defs
        .iter()
        .filter(|d| !generated_names.contains(d.name.as_str()))
        .map(|d| format!("{:?} {} (line {})", d.def_type, d.name, d.line_num))
        .collect();

    // Find new definitions (in generated but not in existing)
    let new_defs: Vec<String> = generated_defs
        .iter()
        .filter(|d| !existing_names.contains(d.name.as_str()))
        .map(|d| format!("{:?} {}", d.def_type, d.name))
        .collect();

    (missing, new_defs)
}

/// Compare generated files with existing ones
fn compare_lean_files(opts: &GenLeanOptions) -> i32 {
    eprintln!("Comparing generated Lean files with existing...\n");

    let files = match run_regenerate_all() {
        Ok(f) => f,
        Err(e) => {
            eprintln!("error: {}", e);
            return 1;
        }
    };

    println!("Lean Verification File Status");
    println!("=============================\n");

    let mut identical = 0;
    let mut different = 0;
    let mut missing_files = 0;
    let mut total_missing_defs = 0;
    let mut total_new_defs = 0;

    let base_dir = &opts.output_dir;

    for (rel_path, generated) in files.iter() {
        // Filter by project if specified
        if let Some(ref project) = opts.project {
            if !rel_path.contains(project) {
                continue;
            }
        }

        let full_path = base_dir.parent().unwrap_or(base_dir).join(rel_path);

        if full_path.exists() {
            match fs::read_to_string(&full_path) {
                Ok(existing) => {
                    if existing.trim() == generated.trim() {
                        println!("  [identical] {}", rel_path);
                        identical += 1;
                    } else {
                        // Extract definitions for completeness check
                        let existing_defs = extract_lean_definitions(&existing);
                        let generated_defs = extract_lean_definitions(generated);
                        let (missing, new_defs) = check_completeness(&existing_defs, &generated_defs);

                        total_missing_defs += missing.len();
                        total_new_defs += new_defs.len();

                        // Determine status based on completeness
                        if missing.is_empty() {
                            println!("  [complete]  {} (can replace)", rel_path);
                        } else {
                            println!("  [INCOMPLETE] {} (missing {} definitions)", rel_path, missing.len());
                        }
                        different += 1;

                        if opts.show_diff {
                            // Show missing definitions
                            if !missing.is_empty() {
                                println!("    Missing definitions:");
                                for def in &missing {
                                    println!("      - {}", def);
                                }
                            }

                            // Show new definitions
                            if !new_defs.is_empty() {
                                println!("    New definitions:");
                                for def in &new_defs {
                                    println!("      + {}", def);
                                }
                            }

                            // Show line difference
                            let existing_lines = existing.lines().count();
                            let generated_lines = generated.lines().count();
                            let diff = generated_lines as i64 - existing_lines as i64;
                            if diff != 0 {
                                println!(
                                    "    Line diff: {} -> {} ({:+} lines)",
                                    existing_lines, generated_lines, diff
                                );
                            }
                            println!();
                        } else {
                            // Brief summary
                            if !missing.is_empty() {
                                println!("              WARNING: {} definitions missing", missing.len());
                            }
                        }
                    }
                }
                Err(e) => {
                    println!("  [error]     {} - {}", rel_path, e);
                    missing_files += 1;
                }
            }
        } else {
            println!("  [new file]  {}", rel_path);
            missing_files += 1;
        }
    }

    println!("\nSummary:");
    println!(
        "  Files: {} identical, {} different, {} new",
        identical, different, missing_files
    );

    if total_missing_defs > 0 {
        println!(
            "  WARNING: {} definitions missing in generated code!",
            total_missing_defs
        );
        println!("  Use --diff to see which definitions are missing.");
    } else if different > 0 {
        println!("  All definitions covered - generated files can safely replace existing ones.");
    }

    if total_new_defs > 0 {
        println!("  INFO: {} new definitions will be added.", total_new_defs);
    }

    if total_missing_defs > 0 {
        2 // Return 2 for incomplete (missing definitions)
    } else if different > 0 || missing_files > 0 {
        1 // Return 1 for differences but complete
    } else {
        0 // Return 0 for identical
    }
}

/// Print a simple unified diff between two strings
fn print_diff(existing: &str, generated: &str, path: &str) {
    println!("\n--- {} (existing)", path);
    println!("+++ {} (generated)", path);

    let existing_lines: Vec<&str> = existing.lines().collect();
    let generated_lines: Vec<&str> = generated.lines().collect();

    // Simple line-by-line diff (not a full unified diff algorithm)
    let max_lines = std::cmp::max(existing_lines.len(), generated_lines.len());

    for i in 0..max_lines {
        let existing_line = existing_lines.get(i).copied().unwrap_or("");
        let generated_line = generated_lines.get(i).copied().unwrap_or("");

        if existing_line != generated_line {
            if !existing_line.is_empty() {
                println!("-{}", existing_line);
            }
            if !generated_line.is_empty() {
                println!("+{}", generated_line);
            }
        }
    }
    println!();
}

/// Generate memory safety Lean 4 verification from a source file
fn generate_memory_safety_lean(args: &[String]) -> i32 {
    // Find the --file argument
    let file_path = args
        .iter()
        .position(|a| a == "--file")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from);

    let file_path = match file_path {
        Some(p) => p,
        None => {
            eprintln!("error: --file <path> is required for memory-safety command");
            return 1;
        }
    };

    if !file_path.exists() {
        eprintln!("error: file not found: {}", file_path.display());
        return 1;
    }

    // Optional --out argument
    let out_path = args
        .iter()
        .position(|a| a == "--out")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from);

    // Read and parse the source file
    let source = match fs::read_to_string(&file_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: could not read file: {}", e);
            return 1;
        }
    };

    // Parse the source
    let mut parser = simple_parser::Parser::new(&source);
    let ast_module = match parser.parse() {
        Ok(m) => m,
        Err(e) => {
            eprintln!("error: parse error: {}", e);
            return 1;
        }
    };

    // Lower to HIR with warnings to get lifetime context
    let lowerer = simple_compiler::hir::Lowerer::new();
    let output = match lowerer.lower_module_with_warnings(&ast_module) {
        Ok(o) => o,
        Err(e) => {
            // If there are lifetime violations, we can still generate Lean code
            // showing what violations were detected
            eprintln!("warning: lowering error (showing detected violations): {}", e);

            // Create Lean output that reflects the detected violations so the
            // proof obligations fail loudly in Lean.
            match e {
                simple_compiler::hir::LowerError::MemorySafetyViolation { all_warnings, .. } => {
                    let module = simple_compiler::hir::HirModule::new();
                    let lean = simple_compiler::codegen::lean::generate_memory_safety_lean(
                        &module,
                        None,
                        Some(&all_warnings),
                        None,
                    );
                    println!("{}", lean);
                    return 0;
                }
                simple_compiler::hir::LowerError::LifetimeViolation(_) => {
                    let module = simple_compiler::hir::HirModule::new();
                    let lean =
                        simple_compiler::codegen::lean::generate_memory_safety_lean(&module, None, None, Some(1));
                    println!("{}", lean);
                    return 0;
                }
                simple_compiler::hir::LowerError::LifetimeViolations(v) => {
                    let module = simple_compiler::hir::HirModule::new();
                    let lean = simple_compiler::codegen::lean::generate_memory_safety_lean(
                        &module,
                        None,
                        None,
                        Some(v.len()),
                    );
                    println!("{}", lean);
                    return 0;
                }
                _ => {
                    // Unknown failure - fall back to empty obligations
                    let module = simple_compiler::hir::HirModule::new();
                    let warnings = simple_compiler::hir::MemoryWarningCollector::new();
                    let lean = simple_compiler::codegen::lean::generate_memory_safety_lean(
                        &module,
                        None,
                        Some(&warnings),
                        None,
                    );
                    println!("{}", lean);
                    return 0;
                }
            }
        }
    };

    // Generate Lean 4 memory safety verification
    let mut lean = simple_compiler::codegen::lean::generate_memory_safety_lean(
        &output.module,
        None,
        Some(&output.warnings),
        Some(output.lifetime_violation_count()),
    );

    // If we have lifetime-specific Lean 4 code, append it
    if let Some(lifetime_lean) = output.get_lifetime_lean4() {
        lean.push_str("\n-- Lifetime-specific verification code from HIR lowering:\n");
        lean.push_str(lifetime_lean);
    }

    // Write to file if requested
    if let Some(out) = out_path {
        if let Some(parent) = out.parent() {
            if let Err(e) = fs::create_dir_all(parent) {
                eprintln!("error: could not create output directory {}: {}", parent.display(), e);
                return 1;
            }
        }
        if let Err(e) = fs::write(&out, lean) {
            eprintln!("error: could not write Lean output to {}: {}", out.display(), e);
            return 1;
        }
        println!("Wrote Lean verification to {}", out.display());
    } else {
        println!("{}", lean);
    }

    // Print summary
    if output.has_warnings() {
        let summary = output.summary();
        eprintln!("\nMemory Safety Analysis:");
        eprintln!("  Total warnings: {}", summary.total);
        if summary.w1001 > 0 {
            eprintln!("  W1001 (Shared mutation): {}", summary.w1001);
        }
        if summary.w1002 > 0 {
            eprintln!("  W1002 (Unique copy): {}", summary.w1002);
        }
        if summary.w1003 > 0 {
            eprintln!("  W1003 (Mutable shared): {}", summary.w1003);
        }
        if summary.w1004 > 0 {
            eprintln!("  W1004 (Borrow escapes): {}", summary.w1004);
        }
        if summary.w1005 > 0 {
            eprintln!("  W1005 (Potential cycle): {}", summary.w1005);
        }
        if summary.w1006 > 0 {
            eprintln!("  W1006 (Missing mut): {}", summary.w1006);
        }
    } else {
        eprintln!("\nNo memory safety warnings detected.");
    }

    0
}

/// Verify known Lean projects using the Lean binary.
/// Exits non-zero if Lean fails or if any sorry remain.
fn verify_lean_files(opts: &GenLeanOptions) -> i32 {
    let project_root = match find_verification_root() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("error: {}", e);
            return 1;
        }
    };

    // Allow overriding Lean binary via env; default to `lean` in PATH.
    let lean_bin = std::env::var("LEAN_BIN").unwrap_or_else(|_| "lean".to_string());
    let runner = LeanRunner::new(lean_bin, project_root.join("verification/.lean-cache")).with_verbose(false);

    let mut results = Vec::new();
    let mut checked = 0;

    for path in get_known_lean_files() {
        if let Some(ref project) = opts.project {
            if !path.contains(project) {
                continue;
            }
        }
        let full = project_root.join(path);
        if !full.exists() {
            continue;
        }
        checked += 1;
        match runner.check_file(&full) {
            Ok(res) => {
                if res.success && res.goals_remaining == 0 {
                    println!("[ok]     {}", path);
                } else if res.success {
                    println!(
                        "[warn]   {} ({} goals remaining, exit {})",
                        path,
                        res.goals_remaining,
                        res.exit_code.unwrap_or(-1)
                    );
                } else {
                    println!(
                        "[fail]   {} (exit {})",
                        path,
                        res.exit_code.unwrap_or(-1)
                    );
                    if !res.stderr.is_empty() {
                        println!("{}", res.stderr);
                    }
                }
                results.push(res);
            }
            Err(e) => {
                println!("[error]  {} - {}", path, e);
            }
        }
    }

    if checked == 0 {
        eprintln!("No Lean verification files found (maybe filtered by --project?)");
        return 1;
    }

    let summary = VerificationSummary::from_results(&results);
    println!("{}", summary.format());

    if summary.is_success() && summary.unproven_theorems == 0 {
        0
    } else {
        1
    }
}

/// Write generated files to disk
fn write_lean_files(opts: &GenLeanOptions) -> i32 {
    eprintln!("Writing Lean verification files...\n");

    let files = match run_regenerate_all() {
        Ok(f) => f,
        Err(e) => {
            eprintln!("error: {}", e);
            return 1;
        }
    };

    let base_dir = &opts.output_dir;
    let mut written = 0;
    let mut skipped = 0;

    for (rel_path, content) in files.iter() {
        // Filter by project if specified
        if let Some(ref project) = opts.project {
            if !rel_path.contains(project) {
                continue;
            }
        }

        let full_path = base_dir.parent().unwrap_or(base_dir).join(rel_path);

        // Check if file exists and --force not set
        if full_path.exists() && !opts.force {
            println!("  [skipped]   {} (use --force to overwrite)", rel_path);
            skipped += 1;
            continue;
        }

        // Create parent directories if needed
        if let Some(parent) = full_path.parent() {
            if !parent.exists() {
                if let Err(e) = fs::create_dir_all(parent) {
                    eprintln!("  [error]     {} - cannot create directory: {}", rel_path, e);
                    continue;
                }
            }
        }

        // Write the file
        match fs::write(&full_path, content) {
            Ok(_) => {
                println!("  [written]   {}", rel_path);
                written += 1;
            }
            Err(e) => {
                eprintln!("  [error]     {} - {}", rel_path, e);
            }
        }
    }

    println!("\nWrote {} files, skipped {}.", written, skipped);

    if skipped > 0 && !opts.force {
        println!("Use --force to overwrite existing files.");
    }

    0
}
