//! Pins seed-interpreter semantic divergences from the self-hosted compiler,
//! documented in doc/08_tracking/bug/seed_optional_query_comparison_divergence_2026-08-16.md
//! (Divergences A and D; B is skipped — see note below).
//!
//! These tests intentionally assert the CURRENT (buggy) seed behavior so the
//! suite stays green today. If either test starts FAILING, that means the
//! underlying seed bug got fixed — do NOT just update the assertion and move
//! on. Instead:
//!   - Divergence A (`.?` yields value-or-nil, not bool): update the ~43
//!     `.? == false` / `.? == true` workaround sites census'd in the bug doc
//!     (including h1_client.spl comments), then flip this test's assertion.
//!   - Divergence D was FIXED on 2026-08-16 (ByteArray concat arms added in
//!     interpreter/expr/ops.rs; the per-byte `.push()` workarounds in
//!     h1_client.spl were reverted). Its test below now asserts the FIXED
//!     behavior and guards against regression.
//!
//! Divergence B (module-private `val` import binds to a non-int sentinel)
//! needs a two-module source (an importer + a separate module declaring a
//! non-pub `val`). The harness here (see packed_byte_interpreter_semantics.rs)
//! only writes a single `main.spl` file into a tempdir, with no support for
//! wiring up a second importable module by `use` path — a second module
//! would need a real package/module layout the harness doesn't build. Skipped
//! for that reason; not covered here.

use std::collections::HashSet;
use std::fs;

fn run_program(source: &str) -> Result<i32, String> {
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.spl");
    fs::write(&main_path, source).unwrap();
    simple_compiler::interpreter::clear_module_cache();
    simple_compiler::interpreter::clear_interpreter_state();
    let module = simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new())
        .map_err(|error| format!("{error:?}"))?;
    simple_compiler::interpreter::set_current_file(Some(main_path.clone()));
    let result = simple_compiler::interpreter::evaluate_module(&module.items).map_err(|error| format!("{error:?}"));
    simple_compiler::interpreter::set_current_file(None);
    result
}

/// Divergence A: `.?` on an optional yields the unwrapped value or nil, not a
/// bool. So `x.? == false` never fires, for a nil optional OR a filled one.
/// The self-hosted compiler treats `.?` as a bool test, so this diverges.
#[test]
fn dot_query_on_nil_optional_never_equals_false() {
    let source = r#"
fn maybe_nil() -> i32?:
    return nil

fn main() -> i32:
    if maybe_nil().? == false:
        # Under self-hosted, `.?` on a nil optional is `false`, so this
        # branch WOULD fire. Under the seed, `.?` yields the wrapped value
        # (nil here), and `nil == false` is false, so this never fires.
        return 1
    return 0
"#;
    // Pin current seed behavior: the guard never fires, so main returns 0.
    assert_eq!(run_program(source), Ok(0));
}

/// Divergence A, filled-optional case: `.?` yields the wrapped value, so
/// `x.? == false` is comparing an int to a bool and is always false too.
#[test]
fn dot_query_on_filled_optional_never_equals_false() {
    let source = r#"
fn maybe_filled() -> i32?:
    return 5

fn main() -> i32:
    if maybe_filled().? == false:
        # Self-hosted: `.?` on a filled optional is `true`; `true == false`
        # is false, so self-hosted also skips this branch (both compilers
        # agree here) -- the real divergence is the nil case above and the
        # `== true` variant, which we also pin for completeness.
        return 1
    if maybe_filled().? == true:
        # Seed: `.?` yields the wrapped int value 5; `5 == true` is false
        # under the seed's value semantics for this comparison, so this
        # branch does not fire either -- pinning current behavior.
        return 2
    return 0
"#;
    assert_eq!(run_program(source), Ok(0));
}

/// Divergence D (FIXED 2026-08-16): reassigning a `var [u8]` accumulator via
/// `+` used to die with "cannot convert array to int" because packed
/// Value::ByteArray had no concat arm and fell through to numeric coercion.
/// Concat arms (ByteArray+ByteArray and mixed Array/ByteArray) were added in
/// interpreter/expr/ops.rs; this now guards against regression.
#[test]
fn while_loop_byte_array_plus_reassign_concats() {
    // Mirrors the real h1_client.spl shape: `bytes: [u8]` built from a
    // runtime/extern source (packed byte-array representation), not an
    // array literal -- `rt_bytes_alloc` gives us that packed representation,
    // same as packed_byte_interpreter_semantics.rs.
    let source = r#"
extern fn rt_bytes_alloc(len: u64) -> [u8]

fn main() -> i32:
    var acc = rt_bytes_alloc(0u64)
    var i = 0
    while i < 3:
        val chunk = rt_bytes_alloc(1u64)
        acc = acc + chunk
        i = i + 1
    return acc.len().to_i32()
"#;
    assert_eq!(run_program(source), Ok(3));
}

/// Divergence D mixed-representation case: `var acc: [u8] = []` lowers the
/// empty literal to a generic Value::Array, so the first `acc + bytes` in a
/// loop is Array + ByteArray. The mixed concat arm must keep this working.
#[test]
fn empty_literal_accumulator_plus_packed_bytes_concats() {
    let source = r#"
extern fn rt_bytes_alloc(len: u64) -> [u8]

fn main() -> i32:
    var acc: [u8] = []
    var i = 0
    while i < 2:
        val chunk = rt_bytes_alloc(2u64)
        acc = acc + chunk
        i = i + 1
    return acc.len().to_i32()
"#;
    assert_eq!(run_program(source), Ok(4));
}
