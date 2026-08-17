//! `use` followed by `.` is a RELATIVE IMPORT, not a field access.
//!
//! Bug: doc/08_tracking/bug/soft_keyword_use_as_ident_broke_all_relative_imports_2026-08-17.md
//! Introduced by 3c4e6551b7a, which added `TokenKind::Use` to the
//! `soft_kw_stmt_as_ident` list in `parser_impl/core.rs` under the rule
//! "`<kw> = …` / `<kw>.field` at statement level is a use of that variable,
//! never the statement form". That rule holds for the other ten keywords and is
//! false for `use`, so every relative import in the tree (200 `^use \.` lines
//! under `src/`) stopped parsing with
//! `Unexpected token: expected identifier, found LBrace`, which took
//! `bin/simple test` down on every spec.
//!
//! The introducing commit's fixtures all passed because none of them parses an
//! import. These are the missing counterpart: the statement form must survive
//! the identifier concession.

use simple_parser::Parser;

fn parse_ok(src: &str) {
    let mut parser = Parser::new(src);
    if let Err(err) = parser.parse() {
        panic!("should parse, got error: {err}\n--- source ---\n{src}");
    }
}

// --- the regression itself -------------------------------------------------

#[test]
fn single_dot_relative_import_with_brace_group_parses() {
    // The exact shape from src/compiler/70.backend/backend/vhdl_backend.spl:14
    parse_ok("use .vhdl.vhdl_builder.{VhdlBuilder}\n");
}

#[test]
fn double_dot_relative_import_with_glob_parses() {
    // The exact shape from src/compiler/70.backend/linker/test/smf_enums_spec.spl:9
    parse_ok("use ..smf_enums.*\n");
}

#[test]
fn relative_import_with_multiple_names_parses() {
    parse_ok("use .a.b.{One, Two, Three}\n");
}

#[test]
fn relative_import_followed_by_a_function_parses() {
    // Guards the recovery path: a mis-parsed import used to resync at the next
    // `fn`, so the error surfaced far from its cause.
    parse_ok("use .vhdl.b.{VhdlBuilder}\nfn main():\n    print(\"ok\")\n");
}

#[test]
fn absolute_import_with_brace_group_still_parses() {
    parse_ok("use compiler.backend.vhdl.vhdl_builder.{VhdlBuilder}\n");
}

// --- the concession the introducing commit wanted must still hold ----------

#[test]
fn use_as_a_variable_name_assigned_still_parses() {
    parse_ok("fn f():\n    var use = 3\n    use = use + 1\n");
}

#[test]
fn export_and_mod_keep_their_dot_concession() {
    // These two share the predicate but have no `.`-leading statement form
    // (0 occurrences of `^export \.` / `^mod \.` in the tree), so they were
    // left in the `.`-peek half and must keep working as field receivers.
    parse_ok("fn f():\n    export.field = 1\n");
    parse_ok("fn f():\n    mod.field = 1\n");
}
