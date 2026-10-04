//! JIT regressions found running the UI showcases on macOS (2026-10-04).
//!
//! 1. A trait method named like a builtin collection method (`size`) was typed
//!    I64 on a trait-typed (ANY) receiver, so `val (w, h) = host.size()`
//!    destructured tagged RuntimeValues as raw ints (1280 read as 10240).
//!    See doc/08_tracking/bug/jit_trait_method_tuple_return_read_as_tagged_ints_2026-10-04.md.
//! 2. With several same-named traits in one flattened module, an impl took the
//!    first trait's (missing) defaults, and calling the default crashed.
//! 3. A trait-typed FIELD receiver calling a default method went through the
//!    vtable type switch, whose miss path needs `rt_method_not_found`
//!    declared; it was not, and codegen panicked.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

const SIZED: &str = r#"
trait SizedHost:
    me size() -> (i32, i32)
    me scale() -> i32

class Box2:
    var w: i32
    var h: i32

impl SizedHost for Box2:
    me size() -> (i32, i32):
        (self.w, self.h)
    me scale() -> i32:
        self.w * 2
"#;

#[test]
fn trait_param_size_tuple_destructures_real_values() {
    let src = format!(
        "{SIZED}\nfn via_trait(host: SizedHost) -> i64:\n    val (w, h) = host.size()\n    w.to_i64() * 10000 + h.to_i64()\n\nfn main() -> i64:\n    val b = Box2(w: 1280, h: 720)\n    via_trait(b)\n"
    );
    assert_eq!(run(&src), 12_800_720);
}

#[test]
fn generic_bound_size_tuple_and_scalar_method_agree_with_direct() {
    let src = format!(
        "{SIZED}\nfn via_generic<H: SizedHost>(host: H) -> i64:\n    val (w, h) = host.size()\n    w.to_i64() * 10000 + h.to_i64() + host.scale().to_i64()\n\nfn main() -> i64:\n    val b = Box2(w: 3, h: 4)\n    via_generic(b)\n"
    );
    assert_eq!(run(&src), 30_004 + 6);
}

#[test]
fn impl_default_from_its_own_same_named_trait() {
    let src = r#"
trait Backend:
    fn name() -> i64

class Other:
    var n: i64

impl Backend for Other:
    fn name() -> i64:
        self.n

trait Backend:
    fn read() -> i64
    me read_twice() -> i64:
        self.read() * 2

class Vk:
    var v: i64

impl Backend for Vk:
    fn read() -> i64:
        self.v

fn main() -> i64:
    val o = Other(n: 1)
    var k = Vk(v: 21)
    k.read_twice() + o.name()
"#;
    assert_eq!(run(src), 43);
}

#[test]
fn trait_field_receiver_default_method_compiles_and_dispatches() {
    let src = r#"
trait Backend:
    fn read() -> i64
    me mark() -> i64:
        self.read() + 100

class A:
    var v: i64

impl Backend for A:
    fn read() -> i64:
        self.v

class B:
    var v: i64

impl Backend for B:
    fn read() -> i64:
        self.v * 10
    me mark() -> i64:
        7

class Holder:
    var backend: Backend

    me poke() -> i64:
        self.backend.mark()

fn main() -> i64:
    var h1 = Holder(backend: A(v: 1))
    var h2 = Holder(backend: B(v: 2))
    h1.poke() * 1000 + h2.poke()
"#;
    assert_eq!(run(src), 101_007);
}

const OPT_SRC: &str = r#"
class Session:
    var dev: i64

    me valid() -> bool:
        self.dev > 0

class Backend:
    var owns: bool
    var session: Session

class Engine:
    var vk: Backend?

    me read() -> i64:
        val active = self.vk
        if active == nil:
            return -1
        val parent = active
        if not parent.owns or not parent.session.valid():
            return -2
        parent.session.dev
"#;

/// 5. `val p = opt` after a nil check, then `p.field`: a boxed `Some(x)` was
///    read as if it were `x` (segfault in Engine2D.create_shared_vulkan_offscreen).
#[test]
fn optional_struct_field_read_after_nil_check_unwraps_boxed_some() {
    let src = format!("{OPT_SRC}\nfn main() -> i64:\n    val e = Engine(vk: Some(Backend(owns: true, session: Session(dev: 77))))\n    e.read()\n");
    assert_eq!(run(&src), 77);
}

#[test]
fn optional_struct_field_read_handles_nil_and_raw_payload() {
    let src = format!(
        "{OPT_SRC}\nfn make(b: Backend) -> Backend?:\n    b\n\nfn main() -> i64:\n    val none = Engine(vk: nil)\n    val raw = Engine(vk: make(Backend(owns: true, session: Session(dev: 5))))\n    none.read() * 100 + raw.read()\n"
    );
    assert_eq!(run(&src), -100 + 5);
}

/// 6. `[u8] + [u8]` (the SPIR-V head+tail blob) came back as garbage bytes.
#[test]
fn byte_array_concat_keeps_bytes() {
    let src = r#"
fn head() -> [u8]:
    [0x03u8, 0x02u8, 0x23u8, 0x07u8]

fn tail() -> [u8]:
    [0x01u8, 0x00u8, 0xFFu8]

fn main() -> i64:
    val c = head() + tail()
    var acc: i64 = c.len()
    for x in c:
        acc = acc * 7 + x.to_i64()
    acc
"#;
    let expected = [3i64, 2, 35, 7, 1, 0, 255].iter().fold(7i64, |acc, x| acc * 7 + x);
    assert_eq!(run(src), expected);
}

/// 4. A flattened private helper `_i64` (`__spl_flat_<stem>_<hash>___i64`)
///    decayed to the `i64` builtin in `compile_call`, so `_i64(width)`
///    returned 0 and the Vulkan framebuffer allocation got size 0.
#[test]
fn flattened_underscore_helper_is_called_not_mistaken_for_builtin() {
    let src = r#"
fn __spl_flat_vk_spl_0123456789abcdef___i64(v: i32) -> i64:
    v as i64

fn area(w: i32, h: i32) -> i64:
    __spl_flat_vk_spl_0123456789abcdef___i64(w) * __spl_flat_vk_spl_0123456789abcdef___i64(h) * 4

fn main() -> i64:
    area(320, 240)
"#;
    assert_eq!(run(src), 307_200);
}
