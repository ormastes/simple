//! Top-level `@when(...)` / `@elif(...)` / `@else:` / `@end` conditional
//! compilation, evaluated against an explicit target.

use simple_parser::ast::Node;
use simple_parser::Parser;

const FIXTURE: &str = include_str!("../../../../test/fixtures/conditional_compile/when_blocks.spl");

fn parse_for(source: &str, os: &str, arch: &str) -> simple_parser::ast::Module {
    Parser::new_for_target(source, os, arch)
        .parse()
        .unwrap_or_else(|e| panic!("parse for {os}/{arch} failed: {e:?}"))
}

/// Names of all top-level functions/externs, and the string each function returns.
fn functions(module: &simple_parser::ast::Module) -> Vec<(String, String)> {
    module
        .items
        .iter()
        .filter_map(|item| match item {
            Node::Function(f) => {
                // Each fixture function body is one string literal on the next line.
                let ret = FIXTURE.lines().nth(f.span.line).unwrap_or("").trim().trim_matches('"');
                Some((f.name.clone(), ret.to_string()))
            }
            Node::Extern(e) => Some((e.name.clone(), "extern".to_string())),
            _ => None,
        })
        .collect()
}

fn returned(module: &simple_parser::ast::Module, name: &str) -> String {
    let matches: Vec<_> = functions(module).into_iter().filter(|(n, _)| n == name).collect();
    assert_eq!(matches.len(), 1, "exactly one `{name}` must survive: {matches:?}");
    matches[0].1.clone()
}

#[test]
fn windows_branch_active() {
    let m = parse_for(FIXTURE, "windows", "x86_64");
    assert_eq!(returned(&m, "platform_name"), "windows");
    assert_eq!(returned(&m, "arch_name"), "windows-other");
    assert!(functions(&m).iter().any(|(n, _)| n == "rt_win_only"));
}

#[test]
fn nested_windows_arm64() {
    let m = parse_for(FIXTURE, "windows", "aarch64");
    assert_eq!(returned(&m, "arch_name"), "windows-arm64");
}

#[test]
fn elif_linux_aarch64() {
    let m = parse_for(FIXTURE, "linux", "aarch64");
    assert_eq!(returned(&m, "platform_name"), "linux-aarch64");
    assert_eq!(returned(&m, "arch_name"), "risc-or-arm");
    assert!(!functions(&m).iter().any(|(n, _)| n == "rt_win_only"));
}

#[test]
fn non_windows_targets_take_unix_or_else() {
    for (os, arch, platform, arch_name) in [
        ("linux", "x86_64", "unix", "other"),
        ("macos", "aarch64", "unix", "risc-or-arm"),
        ("freebsd", "x86_64", "unix", "other"),
        ("simpleos", "riscv64", "unix", "risc-or-arm"),
        ("none", "x86_64", "other", "other"),
    ] {
        let m = parse_for(FIXTURE, os, arch);
        assert_eq!(returned(&m, "platform_name"), platform, "{os}/{arch}");
        assert_eq!(returned(&m, "arch_name"), arch_name, "{os}/{arch}");
    }
}

#[test]
fn line_numbers_preserved_after_skipped_branches() {
    let m = parse_for(FIXTURE, "linux", "x86_64");
    let main = m
        .items
        .iter()
        .find_map(|i| match i {
            Node::Function(f) if f.name == "main" => Some(f),
            _ => None,
        })
        .expect("main");
    let expected = FIXTURE.lines().position(|l| l.starts_with("fn main")).unwrap() + 1;
    assert_eq!(main.span.line, expected);
}

#[test]
fn real_windows_redirected_process_parses_for_all_targets() {
    let src = include_str!("../../../../src/lib/nogc_sync_mut/io/windows_redirected_process.spl");
    for os in ["windows", "linux", "macos", "freebsd", "simpleos"] {
        for arch in ["x86_64", "aarch64", "riscv64"] {
            parse_for(src, os, arch);
        }
    }
}
