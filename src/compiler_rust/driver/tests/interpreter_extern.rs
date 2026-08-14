//! Interpreter tests - extern

use simple_driver::interpreter::run_code;
use std::collections::HashSet;
use std::fs;
use tempfile::tempdir;

struct InterpretedResult {
    exit_code: i32,
}

fn run_interpreted_code(source: &str) -> Result<InterpretedResult, String> {
    let dir = tempdir().map_err(|error| error.to_string())?;
    let main_path = dir.path().join("main.spl");
    fs::write(&main_path, source).map_err(|error| error.to_string())?;
    simple_compiler::interpreter::clear_module_cache();
    simple_compiler::interpreter::clear_interpreter_state();
    let module = simple_compiler::pipeline::module_loader::load_module_with_imports(
        &main_path,
        &mut HashSet::new(),
    )
    .map_err(|error| format!("{error:?}"))?;
    simple_compiler::interpreter::set_current_file(Some(main_path.clone()));
    let result = simple_compiler::interpreter::evaluate_module(&module.items)
        .map(|exit_code| InterpretedResult { exit_code })
        .map_err(|error| format!("{error:?}"));
    simple_compiler::interpreter::set_current_file(None);
    result
}

#[test]
fn interpreter_error_handling_syntax() {
    let result = run_code("invalid syntax here @#$", &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_error_handling_undefined_variable() {
    let result = run_code("main = undefined_var", &[], "");
    assert!(result.is_err());
}

#[test]
fn interpreter_extern_abs() {
    let code = r#"
extern fn abs(x) -> i64

main = abs(-42)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn interpreter_extern_min_max() {
    let code = r#"
extern fn min(a, b) -> i64
extern fn max(a, b) -> i64

let a = min(10, 20)
let b = max(10, 20)
main = a + b
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 30); // 10 + 20
}

#[test]
fn interpreter_extern_sqrt() {
    let code = r#"
extern fn sqrt(x) -> i64

main = sqrt(16)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 4);
}

#[test]
fn interpreter_extern_pow() {
    let code = r#"
extern fn pow(base, exp) -> i64

main = pow(2, 5)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 32); // 2^5 = 32
}

#[test]
fn interpreter_extern_to_int() {
    let code = r#"
extern fn to_int(x) -> i64

main = to_int(true) + to_int(false)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 1); // true=1, false=0
}

#[test]
fn interpreter_extern_rt_bytes_u8_at_preserves_typed_u8_push() {
    let code = r#"
extern fn rt_bytes_u8_at(arr: [u8], idx: i64) -> i64

fn main() -> i32:
    val v: u8 = 0x2du8
    var a: [u8] = []
    a.push(v)
    return rt_bytes_u8_at(a, 0).to_i32()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 45);
}

#[test]
fn interpreter_byte_array_identifier_mutators_write_back_with_cow() {
    let writeback = run_interpreted_code(
        r#"
extern fn rt_byte_array_new(len: i64) -> [u8]
extern fn rt_bytes_u8_at(arr: [u8], idx: i64) -> i64

fn main() -> i32:
    var bytes = rt_byte_array_new(0)
    bytes.push(0x2du8)
    return (bytes.len() * 10 + rt_bytes_u8_at(bytes, 0)).to_i32()
"#,
    )
    .unwrap();
    assert_eq!(
        writeback.exit_code, 55,
        "identifier receiver must be rebound after push"
    );

    let cow = run_interpreted_code(
        r#"
extern fn rt_byte_array_new(len: i64) -> [u8]
extern fn rt_bytes_u8_at(arr: [u8], idx: i64) -> i64

fn main() -> i32:
    var bytes = rt_byte_array_new(1)
    var alias = bytes
    bytes.push(0x09u8)
    return (alias.len() * 100 + rt_bytes_u8_at(alias, 0) * 10 + rt_bytes_u8_at(bytes, 1)).to_i32()
"#,
    )
    .unwrap();
    assert_eq!(
        cow.exit_code, 109,
        "mutating one packed-byte alias must preserve its content and length"
    );

    let pop_writeback = run_interpreted_code(
        r#"
extern fn rt_byte_array_new(len: i64) -> [u8]

fn main() -> i32:
    var bytes = rt_byte_array_new(0)
    bytes.push(0x07u8)
    val removed = bytes.pop()
    return (removed.to_i64() * 10 + bytes.len()).to_i32()
"#,
    )
    .unwrap();
    assert_eq!(
        pop_writeback.exit_code, 70,
        "pop must return the removed byte and trim the binding"
    );
}

#[test]
fn interpreter_byte_array_identifier_mutators_cover_packed_extend_and_structural_updates() {
    let packed_extend = run_interpreted_code(
        r#"
extern fn rt_byte_array_new(len: i64) -> [u8]
extern fn rt_bytes_u8_at(arr: [u8], idx: i64) -> i64

fn main() -> i32:
    var bytes = rt_byte_array_new(0)
    var more = rt_byte_array_new(0)
    bytes.push(0x01u8)
    more.push(0x02u8)
    more.push(0x03u8)
    bytes.extend(more)
    return (bytes.len() * 10 + rt_bytes_u8_at(bytes, 2)).to_i32()
"#,
    )
    .unwrap();
    assert_eq!(
        packed_extend.exit_code, 33,
        "packed [u8] extend must retain packed receiver semantics"
    );

    let structural_updates = run_interpreted_code(
        r#"
extern fn rt_byte_array_new(len: i64) -> [u8]
extern fn rt_bytes_u8_at(arr: [u8], idx: i64) -> i64

fn main() -> i32:
    var bytes = rt_byte_array_new(0)
    bytes.append(0x01u8)
    bytes.push(0x03u8)
    bytes.insert(1, 0x02u8)
    val removed = bytes.remove(1)
    val score = removed.to_i64() * 100 + bytes.len() * 10 + rt_bytes_u8_at(bytes, 1)
    bytes.clear()
    return (score + bytes.len()).to_i32()
"#,
    )
    .unwrap();
    assert_eq!(
        structural_updates.exit_code, 223,
        "append/insert/remove/clear must update the identifier receiver"
    );
}

#[test]
fn interpreter_byte_array_identifier_mutators_widen_on_non_u8_elements() {
    let widened = run_interpreted_code(
        r#"
extern fn rt_byte_array_new(len: i64) -> [u8]

fn main() -> i32:
    var bytes = rt_byte_array_new(0)
    bytes.push(0x01u8)
    bytes.insert(1, "widen")
    bytes.append(0x02u8)
    return bytes.len().to_i32()
"#,
    )
    .unwrap();
    assert_eq!(
        widened.exit_code, 3,
        "a non-u8 identifier mutation must widen once and keep the rebound generic array"
    );
}

#[test]
fn interpreter_byte_array_identifier_mutators_reject_immutable_receivers() {
    let constant = run_interpreted_code(
        r#"
extern fn rt_byte_array_new(len: i64) -> [u8]

fn main() -> i32:
    val bytes = rt_byte_array_new(0)
    bytes.push(0x01u8)
    return 0
"#,
    );
    assert!(
        constant.is_err(),
        "a val ByteArray must reject identifier-mutating methods"
    );

    let frozen = run_interpreted_code(
        r#"
extern fn rt_byte_array_new(len: i64) -> [u8]

fn main() -> i32:
    var bytes = rt_byte_array_new(0)
    val frozen = bytes.freeze()
    frozen.push(0x01u8)
    return 0
"#,
    );
    assert!(
        frozen.is_err(),
        "a frozen ByteArray must reject identifier-mutating methods"
    );
}

#[test]
fn interpreter_byte_array_projected_place_mutators_write_back() {
    let projected = run_interpreted_code(
        r#"
extern fn rt_byte_array_new(len: i64) -> [u8]
extern fn rt_bytes_u8_at(arr: [u8], idx: i64) -> i64

struct ByteHolder:
    bytes: [u8]

fn main() -> i32:
    var holder = ByteHolder(bytes: rt_byte_array_new(0))
    holder.bytes.push(0x11u8)
    holder.bytes.insert(0, 0x07u8)
    val removed = holder.bytes.pop()
    return (removed.to_i64() * 100 + holder.bytes.len() * 10 + rt_bytes_u8_at(holder.bytes, 0)).to_i32()
"#,
    )
    .unwrap();

    assert_eq!(
        projected.exit_code, 1717,
        "mutators on a projected packed-byte place must rebuild and write back the root"
    );
}

// ============ Context Blocks (#35) ============
