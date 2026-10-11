//! Shared `@when`/`@elif`/`@else`/`@end` conformance corpus, run through the
//! Rust seed. The SAME fixtures and expectations are run through the
//! pure-Simple preprocessor by
//! `test/01_unit/compiler/frontend/when_block_conformance_spec.spl`; the two
//! compilers must agree on every row.

use simple_parser::cond_compile::{default_target, select_branches};
use simple_parser::Parser;
use std::collections::BTreeSet;
use std::path::PathBuf;
use std::sync::Mutex;

const TARGET_OS: [&str; 6] = ["windows", "linux", "macos", "freebsd", "simpleos", "none"];
const TARGET_ARCH: [&str; 3] = ["x86_64", "aarch64", "riscv64"];

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..")
}

fn corpus_dir() -> PathBuf {
    repo_root().join("test/fixtures/conditional_compile/conformance")
}

fn read_path(path: &PathBuf) -> String {
    std::fs::read_to_string(path)
        .unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
        .replace('\r', "")
}

fn read(name: &str) -> String {
    read_path(&corpus_dir().join(name))
}

/// Every `TAG_[A-Z0-9_]*` token in `text`.
fn tags(text: &str) -> BTreeSet<String> {
    let bytes = text.as_bytes();
    let mut out = BTreeSet::new();
    let mut i = 0;
    while i + 4 <= bytes.len() {
        if &bytes[i..i + 4] == b"TAG_" {
            let mut j = i + 4;
            while j < bytes.len() && (bytes[j].is_ascii_uppercase() || bytes[j].is_ascii_digit() || bytes[j] == b'_') {
                j += 1;
            }
            out.insert(text[i..j].to_string());
            i = j;
        } else {
            i += 1;
        }
    }
    out
}

/// Non-comment, non-empty, tab-split rows of a corpus table, each with
/// exactly `columns` cells (a malformed row is a corpus bug, not a skip).
fn table(name: &str, columns: usize) -> Vec<Vec<String>> {
    read(name)
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(|l| {
            let cols: Vec<String> = l.split('\t').map(|c| c.trim().to_string()).collect();
            assert_eq!(cols.len(), columns, "{name}: malformed row {l:?}");
            cols
        })
        .collect()
}

struct Row {
    fixture: String,
    os: String,
    arch: String,
    expected: BTreeSet<String>,
    warn: bool,
}

fn rows() -> Vec<Row> {
    table("expectations.tsv", 5)
        .into_iter()
        .map(|c| Row {
            fixture: c[0].clone(),
            os: c[1].clone(),
            arch: c[2].clone(),
            expected: if c[3] == "-" { BTreeSet::new() } else { c[3].split(',').map(str::to_string).collect() },
            warn: match c[4].as_str() {
                "-" => false,
                "warn" => true,
                other => panic!("expectations.tsv: unknown diag class {other:?}"),
            },
        })
        .collect()
}

#[test]
fn corpus_selects_expected_branches_and_keeps_line_count() {
    let rows = rows();
    assert!(rows.len() >= 50, "corpus must not be vacuous: {} rows", rows.len());
    let mut failures = Vec::new();
    for row in &rows {
        let source = read(&row.fixture);
        let label = format!("{} {}/{}", row.fixture, row.os, row.arch);
        let all = tags(&source);
        for tag in &row.expected {
            if !all.contains(tag) {
                failures.push(format!("{label}: expected tag {tag} is not in the fixture"));
            }
        }
        let sel = select_branches(&source, &row.os, &row.arch);
        if !sel.balanced {
            failures.push(format!("{label}: unbalanced {:?}", sel.diagnostics));
        }
        if sel.diagnostics.is_empty() == row.warn {
            failures.push(format!("{label}: expected warn={} but diagnostics {:?}", row.warn, sel.diagnostics));
        }
        if sel.source.split('\n').count() != source.split('\n').count() {
            failures.push(format!("{label}: line count changed"));
        }
        let got = tags(&sel.source);
        if got != row.expected {
            failures.push(format!("{label}: expected {:?}, got {:?}", row.expected, got));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn corpus_fixtures_parse_through_the_lexer_mask_for_every_row() {
    for row in rows() {
        let source = read(&row.fixture);
        let module = Parser::new_for_target(&source, &row.os, &row.arch)
            .parse()
            .unwrap_or_else(|e| panic!("{} {}/{}: {e:?}", row.fixture, row.os, row.arch));
        assert!(!module.items.is_empty() || row.expected.is_empty(), "{}: nothing parsed", row.fixture);
    }
}

/// Every structurally malformed fixture is rejected for every target: the
/// mask is unbalanced and the parser fails instead of compiling both branches.
#[test]
fn malformed_corpus_fails_closed_for_every_target() {
    let files: Vec<String> = read("malformed_files.txt")
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(str::to_string)
        .collect();
    assert_eq!(files.len(), 7, "malformed_files.txt must list every malformed fixture");
    for file in &files {
        let source = read(file);
        for os in TARGET_OS {
            for arch in TARGET_ARCH {
                let sel = select_branches(&source, os, arch);
                assert!(!sel.balanced, "{file} {os}/{arch}: must be unbalanced, got {:?}", sel.diagnostics);
                let error = Parser::new_for_target(&source, os, arch)
                    .parse()
                    .expect_err(&format!("{file} {os}/{arch}: must be a parse error"));
                assert!(error.to_string().contains("unbalanced conditional compilation"), "{file}: {error}");
            }
        }
    }
}

#[test]
fn unbalanced_directives_fail_closed_on_the_lexer_path() {
    for source in ["@when(os=\"windows\"):\nval a = 1\n", "@else:\nval a = 1\n", "@end\n", "@elif(linux):\nval a = 1\n"] {
        for os in TARGET_OS {
            let error = Parser::new_for_target(source, os, "x86_64")
                .parse()
                .expect_err("unbalanced block must be a parse error, never both branches");
            assert!(error.to_string().contains("unbalanced conditional compilation"), "{os}: {error}");
        }
    }
}

/// Every real @when-bearing source file selects one parseable branch for
/// every corpus target.
#[test]
fn owner_files_parse_for_every_corpus_target() {
    let files: Vec<String> = read("owner_files.txt")
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(str::to_string)
        .collect();
    assert_eq!(files.len(), 9, "owner_files.txt must list every @when owner");
    for file in &files {
        let source = read_path(&repo_root().join(file));
        assert!(source.contains("@when("), "{file}: no longer carries @when; update owner_files.txt");
        for os in TARGET_OS {
            for arch in TARGET_ARCH {
                let sel = select_branches(&source, os, arch);
                assert!(sel.balanced && sel.diagnostics.is_empty(), "{file} {os}/{arch}: {:?}", sel.diagnostics);
                assert_eq!(sel.source.split('\n').count(), source.split('\n').count(), "{file} {os}/{arch}");
                Parser::new_for_target(&source, os, arch)
                    .parse()
                    .unwrap_or_else(|e| panic!("{file} {os}/{arch}: {e:?}"));
            }
        }
    }
}

/// Process environment is global: every test that mutates it holds this.
static ENV_LOCK: Mutex<()> = Mutex::new(());

struct EnvGuard(Vec<(&'static str, Option<String>)>);

impl EnvGuard {
    fn set(vars: [(&'static str, &str); 3]) -> Self {
        let saved = vars.iter().map(|(k, _)| (*k, std::env::var(k).ok())).collect();
        for (key, value) in vars {
            if value == "-" {
                std::env::remove_var(key);
            } else {
                std::env::set_var(key, value);
            }
        }
        Self(saved)
    }
}

impl Drop for EnvGuard {
    fn drop(&mut self) {
        for (key, value) in self.0.drain(..) {
            match value {
                Some(v) => std::env::set_var(key, v),
                None => std::env::remove_var(key),
            }
        }
    }
}

#[test]
fn env_driven_target_selection_matches_the_corpus() {
    let _lock = ENV_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    let rows = table("env_targets.tsv", 5);
    assert!(rows.len() >= 9, "env corpus must not be vacuous");
    let os_else = read("os_else.spl");
    for row in rows {
        let _env = EnvGuard::set([
            ("SIMPLE_TARGET_OS", &row[0]),
            ("SIMPLE_TARGET_ARCH", &row[1]),
            ("SIMPLE_NATIVE_BUILD_TARGET", &row[2]),
        ]);
        let label = format!("os={} arch={} triple={}", row[0], row[1], row[2]);
        assert_eq!(default_target(), (row[3].as_str(), row[4].as_str()), "{label}");
        // Parser::new evaluates against default_target(): the surviving
        // branch of os_else.spl is decided by the environment alone.
        let module = Parser::new(&os_else).parse().unwrap_or_else(|e| panic!("{label}: {e:?}"));
        assert_eq!(module.items.len(), 2, "{label}: exactly label + main must survive");
        let (os, arch) = default_target();
        let expected = if row[3] == "windows" { "TAG_WINDOWS" } else { "TAG_OTHER" };
        assert_eq!(tags(&select_branches(&os_else, os, arch).source), BTreeSet::from([expected.to_string()]), "{label}");
    }
}
