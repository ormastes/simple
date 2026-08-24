//! Memory ratchet for the AST node size.
//!
//! `Node` and `Expr` are stored BY VALUE in `Vec<Node>` / `Vec<Expr>`, so every
//! element of every block pays `size_of` of the LARGEST variant, whatever it
//! actually is. Measured 2026-08-23 on the seed: compiling the 807-module
//! `src/app/cli/bootstrap_main.spl` closure (14 MB of source) climbs to
//! 1567 MB RSS in the first ~3.5 s of module load + parse and then sits
//! perfectly FLAT for the remaining ~18 s of the semantic phase — the whole
//! closure's AST is retained live for the entire compile
//! (`hir/lower/import_loader.rs` `IMPORTED_MODULE_AST`), so per-node bytes
//! multiply straight into peak RSS. earlyoom kills `simple` on this box at
//! ~3.7-4.0 GiB, so per-node size is a memory-safety budget, not a nicety.
//!
//! Before the fix `Node` was 936 bytes, set single-handedly by `FunctionDef`
//! (936) — driven by two rarely-populated inline fields, `contract:
//! Option<ContractBlock>` (336 B) and `return_constraint: Option<Expr>`
//! (112 B). Boxing both costs 8 bytes each when absent. This test FAILS on
//! the pre-fix tree.
use simple_parser::ast::{Expr, FunctionDef, Node};

/// Pre-fix actuals: Node 936, FunctionDef 936. Budgets sit just above the
/// post-fix actuals so a fat new inline field trips this immediately.
const NODE_BUDGET: usize = 560;
const FUNCTION_DEF_BUDGET: usize = 560;
const EXPR_BUDGET: usize = 128;

#[test]
fn node_stays_within_memory_budget() {
    let node = std::mem::size_of::<Node>();
    let func = std::mem::size_of::<FunctionDef>();
    let expr = std::mem::size_of::<Expr>();
    eprintln!("size_of::<Node>()        = {node}  (budget {NODE_BUDGET})");
    eprintln!("size_of::<FunctionDef>() = {func}  (budget {FUNCTION_DEF_BUDGET})");
    eprintln!("size_of::<Expr>()        = {expr}  (budget {EXPR_BUDGET})");
    assert!(node <= NODE_BUDGET, "size_of::<Node>() = {node} B exceeds the {NODE_BUDGET} B budget; every AST node in the retained 807-module closure pays this");
    assert!(
        func <= FUNCTION_DEF_BUDGET,
        "size_of::<FunctionDef>() = {func} B exceeds the {FUNCTION_DEF_BUDGET} B budget; it sets size_of::<Node>()"
    );
    assert!(
        expr <= EXPR_BUDGET,
        "size_of::<Expr>() = {expr} B exceeds the {EXPR_BUDGET} B budget"
    );
}

/// Neighbour test, same defect class: the two boxed fields must stay boxed.
/// An `Option<T>` that is `None` in the overwhelming majority of functions must
/// cost a pointer, not `size_of::<T>()`.
#[test]
fn rarely_populated_function_fields_are_indirect() {
    // If either field is ever un-boxed these regain 336 B / 112 B inline.
    let f = FunctionDef {
        span: simple_parser::token::Span {
            start: 0,
            end: 0,
            line: 1,
            column: 1,
        },
        name: String::new(),
        generic_params: Vec::new(),
        params: Vec::new(),
        return_type: None,
        where_clause: Default::default(),
        body: Default::default(),
        visibility: Default::default(),
        effects: Vec::new(),
        decorators: Vec::new(),
        attributes: Vec::new(),
        doc_comment: None,
        contract: None,
        is_abstract: false,
        is_sync: false,
        bounds_block: None,
        is_static: false,
        is_me_method: false,
        is_generator: false,
        return_constraint: None,
        is_generic_template: false,
        specialization_of: None,
        type_bindings: Default::default(),
    };
    // `Option<Box<_>>` is niche-optimised to one pointer.
    assert_eq!(
        std::mem::size_of_val(&f.contract),
        8,
        "contract must be Option<Box<ContractBlock>> (8 B), not an inline 336 B ContractBlock"
    );
    assert_eq!(
        std::mem::size_of_val(&f.return_constraint),
        8,
        "return_constraint must be Option<Box<Expr>> (8 B), not an inline 112 B Expr"
    );
}
