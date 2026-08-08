//! Module-level `val`/`var` must resolve regardless of top-level item order.
//!
//! Regression: `Undefined("undefined identifier: _adv_ascii_vals")` broke the
//! host-WM showcase gate. `Node::Let` was skipped by the checker's first
//! (registration) pass, so a module-level binding only became visible once the
//! second pass walked past it -- making name resolution depend on top-level
//! item order. Functions and classes are pre-registered precisely so they can
//! forward-reference each other; module-level bindings must behave the same.
//!
//! Both orders are asserted in every case so a future regression cannot be
//! mistaken for "the declaration-first form also stopped working".

use simple_parser::Parser;
use simple_type::check;

fn check_src(src: &str) -> Result<(), String> {
    let mut parser = Parser::new(src);
    let module = parser.parse().map_err(|e| format!("parse error: {e:?}"))?;
    check(&module.items).map_err(|e| format!("{e:?}"))
}

/// Every initializer shape, in both orders. The initializer shape is
/// deliberately varied because the original report blamed the repeat-array
/// literal (`[-1; 95]`); it is in fact irrelevant -- order is the only factor.
const SHAPES: &[(&str, &str)] = &[
    ("scalar", "var g: i32 = -1"),
    ("empty_array", "var g: [i32] = []"),
    ("repeat_array", "var g: [i32] = [-1; 95]"),
    ("array_literal", "var g: [i32] = [1, 2, 3]"),
    ("runtime_call", "var g: i32 = mk()"),
    ("text_literal", "var g: text = \"\""),
    ("val_scalar", "val g: i32 = -1"),
    ("val_repeat_array", "val g: [i32] = [-1; 95]"),
];

fn decl_then_reader(decl: &str) -> String {
    format!("fn mk() -> i32:\n    7\n\n{decl}\n\nfn rd() -> i32:\n    print(g)\n    0\n")
}

fn reader_then_decl(decl: &str) -> String {
    format!("fn mk() -> i32:\n    7\n\nfn rd() -> i32:\n    print(g)\n    0\n\n{decl}\n")
}

#[test]
fn module_level_binding_resolves_when_declared_before_reader() {
    for (name, decl) in SHAPES {
        assert!(
            check_src(&decl_then_reader(decl)).is_ok(),
            "{name}: declaration-before-reader must type check",
        );
    }
}

#[test]
fn module_level_binding_resolves_when_declared_after_reader() {
    for (name, decl) in SHAPES {
        let err = check_src(&reader_then_decl(decl));
        assert!(
            err.is_ok(),
            "{name}: module-level binding must be visible to a function \
             declared before it, but got: {}",
            err.unwrap_err(),
        );
    }
}

/// The shape that was blamed in the original report must behave exactly like a
/// plain scalar in both orders -- pinning the actual root cause (item order)
/// rather than the initializer form.
#[test]
fn repeat_array_initializer_behaves_like_scalar_in_both_orders() {
    for decl in ["var g: [i32] = [-1; 95]", "var g: i32 = -1"] {
        assert!(check_src(&decl_then_reader(decl)).is_ok(), "{decl}: decl-first");
        assert!(check_src(&reader_then_decl(decl)).is_ok(), "{decl}: reader-first");
    }
}

/// Mirrors the real `font_renderer.spl` preamble: several module-level
/// bindings of mixed initializer shape, read by a function, with the whole
/// block placed before the module's `use` statements.
#[test]
fn font_renderer_preamble_shape_resolves() {
    let src = concat!(
        "val _ADV_ASCII_LO: i32 = 32\n",
        "val _ADV_ASCII_HI: i32 = 126\n",
        "var _adv_ascii_identity: text = \"\"\n",
        "var _adv_ascii_size: i32 = -1\n",
        "var _adv_ascii_vals: [i32] = [-1; 95]\n",
        "var _adv_overflow_identity: [text] = []\n",
        "\n",
        "fn _adv_cache_lookup(identity: text, font_size: i32, codepoint: i32) -> i32:\n",
        "    if codepoint >= _ADV_ASCII_LO and codepoint <= _ADV_ASCII_HI:\n",
        "        if identity == _adv_ascii_identity and font_size == _adv_ascii_size:\n",
        "            return _adv_ascii_vals[codepoint - _ADV_ASCII_LO]\n",
        "        return -1\n",
        "    -1\n",
    );
    assert!(check_src(src).is_ok(), "font_renderer preamble must type check");

    // Same declarations, reader hoisted above them.
    let reordered = concat!(
        "fn _adv_cache_lookup(identity: text, font_size: i32, codepoint: i32) -> i32:\n",
        "    if codepoint >= _ADV_ASCII_LO and codepoint <= _ADV_ASCII_HI:\n",
        "        if identity == _adv_ascii_identity and font_size == _adv_ascii_size:\n",
        "            return _adv_ascii_vals[codepoint - _ADV_ASCII_LO]\n",
        "        return -1\n",
        "    -1\n",
        "\n",
        "val _ADV_ASCII_LO: i32 = 32\n",
        "val _ADV_ASCII_HI: i32 = 126\n",
        "var _adv_ascii_identity: text = \"\"\n",
        "var _adv_ascii_size: i32 = -1\n",
        "var _adv_ascii_vals: [i32] = [-1; 95]\n",
        "var _adv_overflow_identity: [text] = []\n",
    );
    let err = check_src(reordered);
    assert!(
        err.is_ok(),
        "font_renderer preamble must resolve with the reader hoisted, got: {}",
        err.unwrap_err(),
    );
}
