// Regression: a `val`/`var` declared inside a BDD `it` body (a block closure)
// must shadow a same-named module-level binding.
//
// Before the fix the block-closure Let arm bound the name with `Env::insert`
// only, leaving `is_local` false, and the identifier read prefers
// MODULE_GLOBALS for non-local names — so the body local read back as the
// module global. In real specs the global was an imported module namespace
// (`use compiler.core.types.{...}` binds `types`; `use std.spec.*` binds
// `spec`), and `types.len()` inside the `it` returned the module's export
// count. Surfaced by test/01_unit/compiler/interpreter/mirror_omitted_field_zero_fill_spec.spl.

use simple_compiler::interpreter::evaluate_module;
use simple_parser::Parser;

fn parse_and_eval(source: &str) -> i32 {
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse");
    evaluate_module(&module.items).expect("eval")
}

#[test]
fn it_body_val_shadows_module_global() {
    let source = r#"
var captured = 0
val types = 99
describe "g":
    it "x":
        val types = 7
        captured = types
main = captured
"#;
    assert_eq!(parse_and_eval(source), 7, "the it-body local must win over the module global");
}

#[test]
fn it_body_var_read_modify_write_stays_local() {
    // Pre-fix this returned 100: `spec + 1` read the module global 99.
    let source = r#"
var captured = 0
val spec = 99
describe "g":
    it "x":
        var spec = 5
        spec = spec + 1
        captured = spec
main = captured
"#;
    assert_eq!(parse_and_eval(source), 6, "the it-body var must be read back, not the module global");
}
