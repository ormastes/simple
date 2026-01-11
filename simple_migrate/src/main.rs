#!/usr/bin/env rust-script
//! Simple Language Syntax Migration Tool
//!
//! Migrates from explicit self syntax to Scala-style val/var syntax:
//! - let -> val
//! - let mut -> var
//! - fn method(self, ...) -> fn method(...)
//! - fn method(mut self, ...) -> var fn method(...)
//! - fn constructor() in impl -> static fn constructor()

use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use regex::Regex;
use walkdir::WalkDir;

struct Migration {
    files_processed: usize,
    files_modified: usize,
    backup_dir: PathBuf,
}

impl Migration {
    fn new() -> io::Result<Self> {
        let backup_dir = PathBuf::from(format!(
            ".migration_backup_{}",
            chrono::Local::now().format("%Y%m%d_%H%M%S")
        ));
        fs::create_dir_all(&backup_dir)?;

        Ok(Self {
            files_processed: 0,
            files_modified: 0,
            backup_dir,
        })
    }

    fn migrate_content(&self, content: &str) -> String {
        let mut result = content.to_string();

        // 1. let mut -> var (MUST come before let -> val)
        let let_mut_re = Regex::new(r"\blet\s+mut\b").unwrap();
        result = let_mut_re.replace_all(&result, "var").to_string();

        // 2. let -> val
        let let_re = Regex::new(r"\blet\b").unwrap();
        result = let_re.replace_all(&result, "val").to_string();

        // 3. fn method(mut self) -> var fn method()
        //    Remove mut self parameter and add var prefix
        let mut_self_re = Regex::new(
            r"(?m)^(\s*)fn\s+(\w+)\s*\(\s*mut\s+self\s*\)"
        ).unwrap();
        result = mut_self_re.replace_all(&result, "$1var fn $2()").to_string();

        let mut_self_params_re = Regex::new(
            r"(?m)^(\s*)fn\s+(\w+)\s*\(\s*mut\s+self\s*,\s*"
        ).unwrap();
        result = mut_self_params_re.replace_all(&result, "$1var fn $2(").to_string();

        // 4. fn method(self) -> fn method()
        //    Remove self parameter
        let self_re = Regex::new(
            r"(?m)^(\s*)fn\s+(\w+)\s*\(\s*self\s*\)"
        ).unwrap();
        result = self_re.replace_all(&result, "$1fn $2()").to_string();

        let self_params_re = Regex::new(
            r"(?m)^(\s*)fn\s+(\w+)\s*\(\s*self\s*,\s*"
        ).unwrap();
        result = self_params_re.replace_all(&result, "$1fn $2(").to_string();

        // 5. Add static to constructors in impl blocks
        //    Match common constructor patterns: new, from_*, create_*, default
        //    This is a heuristic - marks fn with no params in impl blocks
        let constructor_re = Regex::new(
            r"(?m)^(\s*)fn\s+(new|default|from_\w+|create_\w+|make_\w+)\s*\(\s*\)\s*->\s*"
        ).unwrap();
        result = constructor_re.replace_all(&result, "$1static fn $2() -> ").to_string();

        result
    }

    fn migrate_file(&mut self, path: &Path) -> io::Result<bool> {
        println!("Processing: {}", path.display());

        let content = fs::read_to_string(path)?;
        let migrated = self.migrate_content(&content);

        if content != migrated {
            // Backup original
            let backup_path = self.backup_dir.join(
                path.strip_prefix(".").unwrap_or(path)
            );
            if let Some(parent) = backup_path.parent() {
                fs::create_dir_all(parent)?;
            }
            fs::write(&backup_path, &content)?;

            // Write migrated content
            fs::write(path, &migrated)?;

            let lines_changed = content.lines().zip(migrated.lines())
                .filter(|(a, b)| a != b)
                .count();

            println!("  ✓ Modified ({} lines changed)", lines_changed);
            Ok(true)
        } else {
            println!("  - No changes");
            Ok(false)
        }
    }

    fn run(&mut self, dir: &Path) -> io::Result<()> {
        println!("=== Simple Language Syntax Migration ===");
        println!("Migrating to Scala-style (val/var) syntax\n");

        for entry in WalkDir::new(dir)
            .follow_links(false)
            .into_iter()
            .filter_entry(|e| {
                let path = e.path();
                !path.starts_with("./target") &&
                !path.starts_with("./.git") &&
                !path.starts_with("./.migration_backup")
            })
        {
            let entry = entry?;
            let path = entry.path();

            if path.extension().and_then(|s| s.to_str()) == Some("spl") {
                self.files_processed += 1;
                if self.migrate_file(path)? {
                    self.files_modified += 1;
                }
            }
        }

        println!("\n=== Migration Complete ===");
        println!("Files processed: {}", self.files_processed);
        println!("Files modified: {}", self.files_modified);
        println!("Backups saved to: {}", self.backup_dir.display());
        println!("\n⚠️  Next steps:");
        println!("1. Review changes: git diff (or jj diff)");
        println!("2. Run tests: cargo test && make check");
        println!("3. Update documentation");
        println!("4. Commit: jj commit -m 'Migrate to Scala-style syntax'");

        Ok(())
    }
}

fn main() -> io::Result<()> {
    let mut migration = Migration::new()?;
    migration.run(Path::new("."))?;
    Ok(())
}
