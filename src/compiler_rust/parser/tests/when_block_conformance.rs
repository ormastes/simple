//! Shared `@when`/`@elif`/`@else`/`@end` conformance corpus, run through the
//! Rust seed. The SAME fixtures and expectations are run through the
//! pure-Simple preprocessor by
//! `test/01_unit/compiler/frontend/when_block_conformance_spec.spl`; the two
//! compilers must agree on every row.

use simple_parser::cond_compile::select_branches;
use simple_parser::Parser;
use std::collections::BTreeSet;
use std::path::PathBuf;

fn corpus_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../test/fixtures/conditional_compile/conformance")
}

fn read(name: &str) -> String {
    let path = corpus_dir().join(name);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
        .replace('\r', "")
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

struct Row {
    fixture: String,
    os: String,
    arch: String,
    expected: BTreeSet<String>,
}

fn rows() -> Vec<Row> {
    read("expectations.tsv")
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(|l| {
            let cols: Vec<&str> = l.split('\t').map(str::trim).collect();
            assert_eq!(cols.len(), 4, "malformed expectations row: {l:?}");
            Row {
                fixture: cols[0].to_string(),
                os: cols[1].to_string(),
                arch: cols[2].to_string(),
                expected: if cols[3] == "-" {
                    BTreeSet::new()
                } else {
                    cols[3].split(',').map(str::to_string).collect()
                },
            }
        })
        .collect()
}

#[test]
fn corpus_selects_expected_branches_and_keeps_line_count() {
    let rows = rows();
    assert!(rows.len() >= 40, "corpus must not be vacuous: {} rows", rows.len());
    let mut failures = Vec::new();
    for row in &rows {
        let source = read(&row.fixture);
        let all = tags(&source);
        for tag in &row.expected {
            assert!(all.contains(tag), "{}: expected tag {tag} is not in the fixture", row.fixture);
        }
        let (selected, diagnostics) = select_branches(&source, &row.os, &row.arch);
        let label = format!("{} {}/{}", row.fixture, row.os, row.arch);
        if !diagnostics.is_empty() {
            failures.push(format!("{label}: diagnostics {diagnostics:?}"));
        }
        if selected.split('\n').count() != source.split('\n').count() {
            failures.push(format!("{label}: line count changed"));
        }
        let got = tags(&selected);
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
