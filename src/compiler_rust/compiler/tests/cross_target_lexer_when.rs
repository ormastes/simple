//! `native-build --target <triple>` must select the TARGET's `@when` branches
//! on every parse path, including sources that reach the lexer directly (no
//! text-level strip). Before this test the override only reached the backend:
//! the lexer evaluated `@when` against the host, so a cross build from a
//! Windows host compiled Windows branches into a Linux binary.
//!
//! Own test binary: `set_target_override` is process-global.

use simple_common::target::Target;
use simple_compiler::interpreter::{clear_parsed_source_cache, shared_source};
use simple_compiler::pipeline::cfg_strip::cfg_target;
use simple_compiler::pipeline::native_project::set_target_override;
use simple_parser::ast::Node;
use simple_parser::cond_compile::default_target;
use simple_parser::Parser;

const SRC: &str = "@when(os=\"windows\"):\nfn pick() -> i64:\n    11\n@elif(os=\"linux\" and arch=\"aarch64\"):\nfn pick() -> i64:\n    22\n@else:\nfn pick() -> i64:\n    33\n@end\n";

/// The literal on the line after the single surviving `fn pick`.
fn picked(module: &simple_parser::ast::Module) -> String {
    let fns: Vec<_> = module
        .items
        .iter()
        .filter_map(|item| match item {
            Node::Function(f) if f.name == "pick" => Some(f.span.line),
            _ => None,
        })
        .collect();
    assert_eq!(fns.len(), 1, "exactly one `pick` must survive, got {fns:?}");
    SRC.lines().nth(fns[0]).unwrap().trim().to_string()
}

#[test]
fn explicit_cross_target_selects_target_branches_on_the_lexer_path() {
    let host_os = Target::host().os.name();
    set_target_override(Target::parse("aarch64-unknown-linux-gnu").expect("triple"));

    // The override is exported like the pure-Simple native-build CLI does,
    // so worker children and the lexer's env-driven default see it.
    assert_eq!(std::env::var("SIMPLE_NATIVE_BUILD_TARGET").as_deref(), Ok("aarch64-linux"));
    assert_eq!(default_target(), ("linux", "aarch64"));
    assert_eq!((cfg_target().os.as_str(), cfg_target().arch.as_str()), ("linux", "aarch64"));

    // Lexer path only: no text strip ran on this source.
    let module = Parser::new(SRC).parse().expect("lexer-path parse");
    assert_eq!(picked(&module), "22", "host is {host_os}; --target must win");

    // Text-strip path (parsed-source cache) agrees.
    clear_parsed_source_cache();
    let path = std::env::temp_dir().join(format!("simple-cross-target-when-{}.spl", std::process::id()));
    std::fs::write(&path, SRC).unwrap();
    let cached = shared_source(&path).ast().expect("cached parse");
    let _ = std::fs::remove_file(&path);
    assert_eq!(picked(&cached), "22");
}
