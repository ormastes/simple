use std::fs;
use std::path::{Path, PathBuf};

use simple_compiler::{build_security_inventory, hir, source_security_violations_sdn_with_modules, SecuritySourceFile};
use simple_parser::Parser;

pub fn run_security(args: &[String]) -> i32 {
    if args.len() < 3 {
        print_usage();
        return 1;
    }

    let command = args[1].as_str();
    let mut output_dir = PathBuf::from("build/security");
    let mut files = Vec::new();
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--out" => {
                if i + 1 >= args.len() {
                    eprintln!("error: --out requires a directory");
                    return 1;
                }
                output_dir = PathBuf::from(&args[i + 1]);
                i += 1;
            }
            arg if arg.starts_with("--out=") => {
                output_dir = PathBuf::from(arg.strip_prefix("--out=").unwrap_or("build/security"));
            }
            arg if arg.starts_with('-') => {
                eprintln!("error: unknown security option: {}", arg);
                return 1;
            }
            path => files.push(PathBuf::from(path)),
        }
        i += 1;
    }

    if files.is_empty() {
        eprintln!("error: security command requires at least one source file");
        return 1;
    }

    let inventory = match build_inventory_for_files(&files) {
        Ok(inventory) => inventory,
        Err(error) => {
            eprintln!("error: {}", error);
            return 1;
        }
    };

    match command {
        "check" => write_inventory(&output_dir, &inventory),
        "matrix" => {
            print!("{}", inventory.access_matrix_sdn);
            0
        }
        "sandbox-manifest" => {
            print!("{}", inventory.sandbox_manifest_sdn);
            0
        }
        "capability-manifest" => {
            print!("{}", inventory.capability_manifest_sdn);
            0
        }
        "aspects" => {
            print!("{}", inventory.security_aspects_spl);
            0
        }
        "aop-lowering" => {
            print!("{}", inventory.security_aop_sdn);
            0
        }
        "audit-gates" => {
            print!("{}", inventory.gate_inventory_md);
            0
        }
        "violations" => {
            print!("{}", inventory.violations_sdn);
            0
        }
        "explain" => {
            println!("security inputs:");
            for file in &files {
                println!("  - {}", file.display());
            }
            println!();
            print!("{}", inventory.gate_inventory_md);
            println!();
            print!("{}", inventory.access_matrix_sdn);
            0
        }
        _ => {
            eprintln!("error: unknown security command: {}", command);
            print_usage();
            1
        }
    }
}

fn build_inventory_for_files(files: &[PathBuf]) -> Result<simple_compiler::SecurityInventory, String> {
    let mut gate_inventory_md = String::new();
    let mut access_matrix_sdn = String::new();
    let mut security_aspects_spl = String::new();
    let mut security_aop_sdn = String::new();
    let mut capability_manifest_sdn = String::new();
    let mut sandbox_manifest_sdn = String::new();
    let mut violations_sdn = String::new();
    let mut source_files = Vec::new();
    let mut modules = Vec::new();

    for file in files {
        let source = fs::read_to_string(file).map_err(|err| format!("failed to read {}: {}", file.display(), err))?;
        source_files.push(SecuritySourceFile {
            path: file.display().to_string(),
            source: source.clone(),
        });
        let mut parser = Parser::new(&source);
        let ast = parser
            .parse()
            .map_err(|err| format!("failed to parse {}: {}", file.display(), err))?;
        let module = hir::lower(&ast).map_err(|err| format!("failed to lower {}: {}", file.display(), err))?;
        let inventory = build_security_inventory(&module);

        append_section(&mut gate_inventory_md, file, &inventory.gate_inventory_md);
        append_section(&mut access_matrix_sdn, file, &inventory.access_matrix_sdn);
        append_section(&mut security_aspects_spl, file, &inventory.security_aspects_spl);
        append_section(&mut security_aop_sdn, file, &inventory.security_aop_sdn);
        append_section(&mut capability_manifest_sdn, file, &inventory.capability_manifest_sdn);
        append_section(&mut sandbox_manifest_sdn, file, &inventory.sandbox_manifest_sdn);
        append_section(&mut violations_sdn, file, &inventory.violations_sdn);
        modules.push(module);
    }

    if !violations_sdn.is_empty() {
        violations_sdn.push('\n');
    }
    violations_sdn.push_str("# source: convention-inferred feature graph\n");
    violations_sdn.push_str(&source_security_violations_sdn_with_modules(&source_files, &modules));

    Ok(simple_compiler::SecurityInventory {
        gate_inventory_md,
        access_matrix_sdn,
        security_aspects_spl,
        security_aop_sdn,
        capability_manifest_sdn,
        sandbox_manifest_sdn,
        violations_sdn,
    })
}

fn append_section(out: &mut String, file: &Path, content: &str) {
    if !out.is_empty() {
        out.push('\n');
    }
    out.push_str(&format!("# source: {}\n", file.display()));
    out.push_str(content);
}

fn write_inventory(output_dir: &Path, inventory: &simple_compiler::SecurityInventory) -> i32 {
    if let Err(error) = fs::create_dir_all(output_dir) {
        eprintln!("error: failed to create {}: {}", output_dir.display(), error);
        return 1;
    }

    let outputs = [
        ("gate_inventory.md", &inventory.gate_inventory_md),
        ("access_matrix.generated.sdn", &inventory.access_matrix_sdn),
        ("security_aspects.generated.spl", &inventory.security_aspects_spl),
        ("security_aop.generated.sdn", &inventory.security_aop_sdn),
        ("capability_manifest.sdn", &inventory.capability_manifest_sdn),
        ("sandbox_manifest.sdn", &inventory.sandbox_manifest_sdn),
        ("violations.sdn", &inventory.violations_sdn),
    ];

    for (name, content) in outputs {
        let path = output_dir.join(name);
        if let Err(error) = fs::write(&path, content) {
            eprintln!("error: failed to write {}: {}", path.display(), error);
            return 1;
        }
    }

    println!("security inventory written to {}", output_dir.display());
    0
}

fn print_usage() {
    eprintln!("Usage:");
    eprintln!("  simple security check <file.spl>... [--out build/security]");
    eprintln!("  simple security matrix <file.spl>...");
    eprintln!("  simple security aspects <file.spl>...");
    eprintln!("  simple security aop-lowering <file.spl>...");
    eprintln!("  simple security capability-manifest <file.spl>...");
    eprintln!("  simple security sandbox-manifest <file.spl>...");
    eprintln!("  simple security audit-gates <file.spl>...");
    eprintln!("  simple security violations <file.spl>...");
    eprintln!("  simple security explain <file.spl>...");
}
