//! Nested trait calls on primitive self retain the selected impl's width.
//! Arithmetic and ordinary runtime integer values remain unchanged.
use simple_compiler::interpreter;
use simple_parser::Parser;

fn run(source: &str) -> i32 {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module = Parser::new(source)
        .parse()
        .expect("primitive self fixture parses");
    interpreter::evaluate_module(&module.items).expect("primitive self fixture executes")
}

#[test]
fn nested_calls_on_narrow_primitive_self_keep_the_impl_owner() {
    assert_eq!(
        run(r#"
trait Inner:
    fn inner() -> i64
trait Outer:
    fn outer() -> i64
impl Inner for i8:
    fn inner() -> i64: 8
impl Inner for i16:
    fn inner() -> i64: 16
impl Inner for i32:
    fn inner() -> i64: 32
impl Inner for i64:
    fn inner() -> i64: 64
impl Outer for i8:
    fn outer(self) -> i64: self.inner()
impl Outer for i16:
    fn outer() -> i64: self.inner()
impl Outer for i32:
    fn outer() -> i64: self.inner()
fn main() -> i32:
    val a: i8 = 7
    val b: i16 = 7
    val c: i32 = 7
    if a.outer() != 8: return 1
    if b.outer() != 16: return 2
    if c.outer() != 32: return 3
    if c + 100 != 107: return 4
    if c.to_text() != "7": return 5
    0
"#),
        0
    );
}

#[test]
fn fallback_impl_self_uses_its_actual_owner_not_the_receivers_width() {
    assert_eq!(
        run(r#"
trait Inner:
    fn inner() -> i64
trait WideOnly:
    fn wide_only() -> i64
impl Inner for i32:
    fn inner() -> i64: 32
impl Inner for i64:
    fn inner() -> i64: 64
impl WideOnly for i64:
    fn wide_only() -> i64: self.inner()
fn main() -> i32:
    val narrow: i32 = 7
    val wide: i64 = 7
    if narrow.wide_only() != 64: return 1
    if wide.wide_only() != 64: return 2
    if narrow.inner() != 32: return 3
    0
"#),
        0
    );
}
