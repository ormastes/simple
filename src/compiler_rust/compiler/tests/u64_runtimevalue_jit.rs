use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

#[test]
fn custom_enum_preserves_u64_erased_boundaries_in_cranelift_jit() {
    let source = r#"
enum Carrier:
    Value(u64)

enum Outer:
    Nested(Carrier)

enum Adjacent:
    Both(u64, i64)

enum SignedCarrier:
    Value(i64)

fn unwrap(value: Carrier) -> u64:
    match value:
        case Carrier.Value(payload): payload

fn unwrap_nested(value: Outer) -> u64:
    match value:
        case Outer.Nested(inner): unwrap(inner)

fn adjacent_ok(value: Adjacent) -> i64:
    match value:
        case Adjacent.Both(unsigned, signed):
            if unsigned == 18446744073709551615u64 and signed == -8:
                return 1
            return 0

fn unwrap_signed(value: SignedCarrier) -> i64:
    match value:
        case SignedCarrier.Value(payload): payload

fn main() -> i64:
    if unwrap(Carrier.Value(0u64)) != 0u64: return 10
    if unwrap(Carrier.Value(1u64)) != 1u64: return 11
    if unwrap(Carrier.Value(2u64)) != 2u64: return 12
    if unwrap(Carrier.Value(3u64)) != 3u64: return 13
    if unwrap(Carrier.Value(4u64)) != 4u64: return 14
    if unwrap(Carrier.Value(5u64)) != 5u64: return 15
    if unwrap(Carrier.Value(6u64)) != 6u64: return 16
    if unwrap(Carrier.Value(7u64)) != 7u64: return 17
    if unwrap(Carrier.Value(2305843009213693952u64)) != 2305843009213693952u64: return 20
    if unwrap(Carrier.Value(9223372036854775808u64)) != 9223372036854775808u64: return 21
    if unwrap(Carrier.Value(18446744073709551615u64)) != 18446744073709551615u64: return 22
    if unwrap_nested(Outer.Nested(Carrier.Value(18446744073709551615u64))) != 18446744073709551615u64: return 23
    if adjacent_ok(Adjacent.Both(18446744073709551615u64, -8)) != 1: return 24
    if (unwrap_signed(SignedCarrier.Value(-8)) >> 2) != -2: return 25
    return 0
"#;

    let ast = Parser::new(source).parse().expect("u64 enum source must parse");
    let hir_module = hir::lower(&ast).expect("u64 enum source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("u64 enum source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("u64 enum MIR must compile");
    let result = unsafe { jit.call_i64_void("main").expect("u64 enum main must execute") };
    assert_eq!(result, 0, "u64 erased-boundary probe failed at case {result}");
}
