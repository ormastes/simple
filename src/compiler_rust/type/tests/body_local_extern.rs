//! Body-local `extern fn` declarations must bind the extern name for the
//! enclosing scope.
//!
//! Regression: `Undefined("undefined identifier: rt_arm64_user_as_create")`
//! made `simple compile <kernel loader/scheduler file> --format=smf` fail on
//! the host (bug doc `seed_cfg_strip_kernel_closure_undefined_externs`): the
//! parser emits `Node::Extern` for `extern fn` declarations inside a function
//! body (kernel files declare their arch externs inside `@cfg(<arch>)`
//! bodies), but the type checker's statement pass had no `Node::Extern` arm,
//! so the declaration fell into the wildcard and the very next call to the
//! extern aborted the whole unit. Top-level externs were unaffected (the
//! module registration pass binds them); body-local ones are now bound by the
//! statement pass with the same fresh-var policy.
//!
//! The `cfg`-gated form is asserted too: on a host whose arch matches the
//! gate (e.g. aarch64 for `@cfg(arm64)`) the body is checked, and the
//! body-local extern must still resolve.

use simple_parser::Parser;
use simple_type::check;

fn check_src(src: &str) -> Result<(), String> {
    let mut parser = Parser::new(src);
    let module = parser.parse().map_err(|e| format!("parse error: {e:?}"))?;
    check(&module.items).map_err(|e| format!("{e:?}"))
}

#[test]
fn body_local_extern_binds_for_enclosing_scope() {
    let src = "\
fn create() -> u64:\n\
\x20   extern fn rt_probe_ext() -> u64\n\
\x20   rt_probe_ext()\n\
\n\
fn main() -> i32:\n\
\x20   val root = create()\n\
\x20   0\n";
    check_src(src).expect("body-local extern declaration must resolve in its body");
}

#[test]
fn body_local_extern_binds_in_cfg_gated_body() {
    // Exactly the shape used by src/os/kernel/memory/user_address_space.spl:
    // the extern is declared inside a per-arch body. Whatever the host arch,
    // at most one variant survives the cfg strip; on the matching host this
    // arm must check cleanly.
    let src = "\
@cfg(x86_64)\n\
fn create() -> u64:\n\
\x20   extern fn rt_probe_ext() -> u64\n\
\x20   rt_probe_ext()\n\
\n\
@cfg(arm64)\n\
fn create() -> u64:\n\
\x20   extern fn rt_probe_ext() -> u64\n\
\x20   rt_probe_ext()\n\
\n\
@cfg(riscv64)\n\
fn create() -> u64:\n\
\x20   extern fn rt_probe_ext() -> u64\n\
\x20   rt_probe_ext()\n\
\n\
fn main() -> i32:\n\
\x20   val root = create()\n\
\x20   0\n";
    check_src(src).expect("body-local extern must resolve in a cfg-gated body");
}

#[test]
fn body_local_extern_does_not_leak_to_module_scope() {
    // The binding is scoped to the enclosing body: a call from ANOTHER
    // function must still report the extern as undefined.
    let src = "\
fn create() -> u64:\n\
\x20   extern fn rt_probe_ext() -> u64\n\
\x20   rt_probe_ext()\n\
\n\
fn other() -> u64:\n\
\x20   rt_probe_ext()\n";
    let err = check_src(src).expect_err("body-local extern must not leak to other functions");
    assert!(
        err.contains("undefined identifier: rt_probe_ext"),
        "expected undefined-identifier error, got: {err}"
    );
}
