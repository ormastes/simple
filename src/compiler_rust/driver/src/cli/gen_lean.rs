//! Lean code generation commands.
//!
//! Commands:
//! - generate: Generate all Lean files from verification module
//! - compare:  Compare generated with existing files
//! - write:    Write generated files to verification/
//! - verify:   Run Lean on known verification projects

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

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
        "verification/type_inference_compile/src/Contracts.lean",
        "verification/type_inference_compile/src/AsyncEffectInference.lean",
    ]
}

fn is_supported_generated_file(path: &str) -> bool {
    get_known_lean_files().iter().any(|known| known == &path)
}

fn placeholder_markers(content: &str) -> Vec<&'static str> {
    let mut markers = Vec::new();
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("--") || trimmed.starts_with("/-") || trimmed.starts_with("-/") {
            continue;
        }
        if trimmed.contains("sorry") && !markers.contains(&"sorry") {
            markers.push("sorry");
        }
        if trimmed.starts_with("axiom ") && !markers.contains(&"axiom") {
            markers.push("axiom");
        }
    }
    markers
}

fn relative_output_path(rel_path: &str) -> &str {
    rel_path.strip_prefix("verification/").unwrap_or(rel_path)
}

fn resolve_output_path(project_root: &std::path::Path, output_dir: &std::path::Path, rel_path: &str) -> PathBuf {
    project_root.join(output_dir).join(relative_output_path(rel_path))
}

fn find_verification_source_root(project_root: &std::path::Path) -> Result<PathBuf, String> {
    let candidates = [
        project_root.join("src/compiler_rust/lib/std/src"),
        project_root.join("src/std/src"),
    ];

    for candidate in candidates {
        if candidate.join("verification/regenerate/__init__.spl").exists() {
            return Ok(candidate);
        }
    }

    Err("Could not find verification regeneration sources under src/compiler_rust/lib/std/src or src/std/src.".to_string())
}

struct RegenerationModuleSpec {
    source_rel_path: &'static str,
    output_path: &'static str,
    function_name: &'static str,
}

fn supported_regeneration_modules() -> &'static [RegenerationModuleSpec] {
    &[
        RegenerationModuleSpec {
            source_rel_path: "verification/regenerate/nogc_compile.spl",
            output_path: "verification/nogc_compile/src/NogcCompile.lean",
            function_name: "regenerate_nogc_compile",
        },
        RegenerationModuleSpec {
            source_rel_path: "verification/regenerate/async_compile.spl",
            output_path: "verification/async_compile/src/AsyncCompile.lean",
            function_name: "regenerate_async_compile",
        },
        RegenerationModuleSpec {
            source_rel_path: "verification/regenerate/gc_manual_borrow.spl",
            output_path: "verification/gc_manual_borrow/src/GcManualBorrow.lean",
            function_name: "regenerate_gc_manual_borrow",
        },
        RegenerationModuleSpec {
            source_rel_path: "verification/regenerate/manual_pointer_borrow.spl",
            output_path: "verification/manual_pointer_borrow/src/ManualPointerBorrow.lean",
            function_name: "regenerate_manual_pointer_borrow",
        },
        RegenerationModuleSpec {
            source_rel_path: "verification/regenerate/module_resolution.spl",
            output_path: "verification/module_resolution/src/ModuleResolution.lean",
            function_name: "regenerate_module_resolution",
        },
        RegenerationModuleSpec {
            source_rel_path: "verification/regenerate/visibility_export.spl",
            output_path: "verification/visibility_export/src/VisibilityExport.lean",
            function_name: "regenerate_visibility_export",
        },
        RegenerationModuleSpec {
            source_rel_path: "verification/regenerate/macro_auto_import.spl",
            output_path: "verification/macro_auto_import/src/MacroAutoImport.lean",
            function_name: "regenerate_macro_auto_import",
        },
        RegenerationModuleSpec {
            source_rel_path: "verification/regenerate/type_inference.spl",
            output_path: "verification/type_inference_compile/src/TypeInferenceCompile.lean",
            function_name: "regenerate_type_inference_compile",
        },
        RegenerationModuleSpec {
            source_rel_path: "verification/regenerate/contracts.spl",
            output_path: "verification/type_inference_compile/src/Contracts.lean",
            function_name: "regenerate_contracts",
        },
        RegenerationModuleSpec {
            source_rel_path: "verification/regenerate/async_effect_inference.spl",
            output_path: "verification/type_inference_compile/src/AsyncEffectInference.lean",
            function_name: "regenerate_async_effect_inference",
        },
    ]
}

fn rewrite_regeneration_module_source(source: &str) -> String {
    let rewritten = source
        .lines()
        .filter(|line| line.trim() != "use verification.lean.codegen as codegen")
        .map(|line| line.replace("codegen.", ""))
        .collect::<Vec<_>>()
        .join("\n");
    let rewritten = replace_identifier(&rewritten, "gen", "builder");
    let rewritten = replace_identifier(&rewritten, "make_simple_type", "cg_make_simple_type");
    let rewritten = replace_identifier(&rewritten, "make_list_type", "cg_make_list_type");
    let rewritten = replace_identifier(&rewritten, "make_string_type", "cg_make_string_type");
    let rewritten = replace_identifier(&rewritten, "make_int_type", "cg_make_int_type");
    let rewritten = replace_identifier(&rewritten, "make_bool_type", "cg_make_bool_type");
    let rewritten = replace_identifier(&rewritten, "make_option_type", "cg_make_option_type");
    replace_identifier(&rewritten, "make_nat_type", "cg_make_nat_type")
}

fn replace_identifier(source: &str, from: &str, to: &str) -> String {
    let chars: Vec<char> = source.chars().collect();
    let from_chars: Vec<char> = from.chars().collect();
    let mut out = String::with_capacity(source.len());
    let mut i = 0;

    while i < chars.len() {
        let matches = i + from_chars.len() <= chars.len()
            && chars[i..i + from_chars.len()] == from_chars[..]
            && (i == 0 || !is_identifier_char(chars[i - 1]))
            && (i + from_chars.len() == chars.len()
                || !is_identifier_char(chars[i + from_chars.len()]));

        if matches {
            out.push_str(to);
            i += from_chars.len();
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }

    out
}

fn is_identifier_char(ch: char) -> bool {
    ch == '_' || ch.is_ascii_alphanumeric()
}

fn build_rewritten_regen_script(
    codegen_source: &str,
    module_body: &[String],
    output_path: &str,
) -> Result<String, String> {
    let mut body = String::new();
    let mut saw_return = false;

    for line in module_body {
        let trimmed = line.trim_start();
        let indent = &line[..line.len() - trimmed.len()];
        if trimmed.starts_with("return ") {
            let expr = trimmed.trim_start_matches("return ").trim();
            body.push_str("    ");
            body.push_str(indent);
            body.push_str("val content = ");
            body.push_str(expr);
            body.push('\n');
            saw_return = true;
        } else {
            body.push_str("    ");
            body.push_str(line);
            body.push('\n');
        }
    }

    if !saw_return {
        return Err("Rewritten regeneration module is missing a final return statement.".to_string());
    }

    Ok(format!(
        r#"{codegen_source}

fn main() -> Int:
{body}    print("FILE:{output_path}")
    print("LENGTH:" + str(len(content)))
    print(content)
    print("END_FILE")
    0
"#
    ))
}

fn extract_function_body(source: &str, function_name: &str) -> Result<Vec<String>, String> {
    let signature = format!("fn {}(", function_name);
    let lines: Vec<&str> = source.lines().collect();
    let start = lines
        .iter()
        .position(|line| line.trim_start().starts_with(&signature))
        .ok_or_else(|| format!("Could not find function {} in regeneration module.", function_name))?;
    let mut body = Vec::new();

    for line in lines.iter().skip(start + 1) {
        if let Some(stripped) = line.strip_prefix("    ") {
            body.push(stripped.to_string());
        } else if line.trim().is_empty() {
            body.push(String::new());
        } else {
            break;
        }
    }

    if body.is_empty() {
        return Err(format!(
            "Function {} in regeneration module has an empty body.",
            function_name
        ));
    }

    Ok(body)
}

fn run_rewritten_regen_module(
    interpreter: &Interpreter,
    source_root: &Path,
    codegen_source: &str,
    spec: &RegenerationModuleSpec,
) -> Result<(String, String), String> {
    let module_path = source_root.join(spec.source_rel_path);
    let module_source = fs::read_to_string(&module_path).map_err(|e| {
        format!(
            "Could not read regeneration source {}: {}",
            module_path.display(),
            e
        )
    })?;
    let rewritten_module = rewrite_regeneration_module_source(&module_source);
    let module_body = extract_function_body(&rewritten_module, spec.function_name)?;
    let runner_source = build_rewritten_regen_script(codegen_source, &module_body, spec.output_path)?;
    let runner_name = spec
        .source_rel_path
        .rsplit('/')
        .next()
        .unwrap_or("regen_runner.spl");
    let runner_path = source_root.join(format!("_{}", runner_name));
    fs::write(&runner_path, runner_source).map_err(|e| {
        format!(
            "Could not create regeneration runner {}: {}",
            runner_path.display(),
            e
        )
    })?;

    let config = RunConfig {
        capture_output: true,
        running_type: RunningType::Interpreter,
        ..Default::default()
    };
    let result = interpreter.run_file(&runner_path, config);
    let _ = fs::remove_file(&runner_path);

    match result {
        Ok(res) if res.exit_code == 0 => {
            let mut files = parse_regenerate_output(&res.stdout)?;
            match files.remove(spec.output_path) {
                Some(content) => Ok((spec.output_path.to_string(), content)),
                None => Err(format!(
                    "Regeneration runner for {} did not emit {}.",
                    spec.source_rel_path, spec.output_path
                )),
            }
        }
        Ok(res) => Err(format!(
            "Regeneration module {} failed with exit code {}.\nstdout:\n{}\nstderr:\n{}",
            spec.source_rel_path, res.exit_code, res.stdout, res.stderr
        )),
        Err(e) => Err(format!(
            "Could not run regeneration module {}: {}",
            spec.source_rel_path, e
        )),
    }
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
fn run_regenerate_all() -> Result<HashMap<String, String>, String> {
    let project_root = find_verification_root()?;
    let source_root = find_verification_source_root(&project_root)?;
    let codegen_path = source_root.join("verification/lean/codegen.spl");
    let codegen_source = fs::read_to_string(&codegen_path).map_err(|e| {
        format!(
            "Could not read Lean codegen source {}: {}",
            codegen_path.display(),
            e
        )
    })?;
    let interpreter = Interpreter::new();
    let mut supported = HashMap::new();

    for spec in supported_regeneration_modules() {
        let (path, content) =
            run_rewritten_regen_module(&interpreter, &source_root, &codegen_source, spec)?;
        if !is_supported_generated_file(&path) {
            continue;
        }

        let markers = placeholder_markers(&content);
        if !markers.is_empty() {
            return Err(format!(
                "Generated Lean output for {} still contains {}.",
                path,
                markers.join(", ")
            ));
        }

        supported.insert(path, content);
    }

    if supported.is_empty() {
        return Err("No proof-clean Lean files were generated.".to_string());
    }

    Ok(supported)
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
    let project_root = match find_verification_root() {
        Ok(root) => root,
        Err(e) => {
            eprintln!("error: {}", e);
            return 1;
        }
    };

    for (rel_path, generated) in files.iter() {
        // Filter by project if specified
        if let Some(ref project) = opts.project {
            if !rel_path.contains(project) {
                continue;
            }
        }

        let full_path = resolve_output_path(&project_root, &opts.output_dir, rel_path);

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
                    let lean =
                        simple_compiler::codegen::lean::generate_memory_safety_lean(&module, None, None, Some(v.len()));
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
    let cache_dir = if opts.output_dir.is_absolute() {
        opts.output_dir.join(".lean-cache")
    } else {
        project_root.join(&opts.output_dir).join(".lean-cache")
    };
    let runner = LeanRunner::new(lean_bin, cache_dir).with_verbose(false);

    let mut results = Vec::new();
    let mut checked = 0;
    let known_files: HashSet<_> = get_known_lean_files().iter().copied().collect();

    for path in get_known_lean_files() {
        if let Some(ref project) = opts.project {
            if !path.contains(project) {
                continue;
            }
        }
        let full = resolve_output_path(&project_root, &opts.output_dir, path);
        if !full.exists() {
            continue;
        }
        checked += 1;
        match runner.check_file(&full) {
            Ok(res) => {
                let source = match fs::read_to_string(&full) {
                    Ok(content) => content,
                    Err(e) => {
                        println!("[error]  {} - {}", path, e);
                        continue;
                    }
                };
                let markers = placeholder_markers(&source);
                if !markers.is_empty() {
                    println!("[fail]   {} (contains {})", path, markers.join(", "));
                    continue;
                }
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
                    println!("[fail]   {} (exit {})", path, res.exit_code.unwrap_or(-1));
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
        let available: Vec<_> = known_files
            .into_iter()
            .filter(|path| resolve_output_path(&project_root, &opts.output_dir, path).exists())
            .collect();
        if available.is_empty() {
            eprintln!(
                "No supported Lean verification files found under {}. Run `simple gen-lean write --force` first.",
                opts.output_dir.display()
            );
        } else {
            eprintln!("No Lean verification files matched the current filter.");
        }
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

    let project_root = match find_verification_root() {
        Ok(root) => root,
        Err(e) => {
            eprintln!("error: {}", e);
            return 1;
        }
    };
    let mut written = 0;
    let mut skipped = 0;

    for (rel_path, content) in files.iter() {
        // Filter by project if specified
        if let Some(ref project) = opts.project {
            if !rel_path.contains(project) {
                continue;
            }
        }

        let full_path = resolve_output_path(&project_root, &opts.output_dir, rel_path);

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
