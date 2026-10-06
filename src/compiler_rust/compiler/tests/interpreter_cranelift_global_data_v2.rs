//! Registered typed-global ABI must emit native object data without functions.
#![cfg(target_os = "linux")]
use object::{Object, ObjectSection, ObjectSymbol};
use simple_compiler::interpreter;
use simple_parser::Parser;

#[test]
fn registered_typed_global_emits_public_initialized_aligned_object_data() {
    let directory = tempfile::tempdir().unwrap();
    let output = directory.path().join("seed-global-v2.o");
    let path = output.to_str().unwrap();
    let source = format!(r#"extern fn rt_string_data(value: text) -> i64
extern fn rt_cranelift_new_aot_module(name: i64, length: i64, target: i64) -> i64
extern fn rt_cranelift_declare_global_data_v2(module: i64, name: i64, length: i64, type_code: i64, initial_bits: i64, linkage: i64, alignment: i64) -> i64
extern fn rt_cranelift_emit_object_raw(module: i64, path: i64, length: i64) -> bool
extern fn rt_cranelift_free_module(module: i64)
val module_name = "seed-global-v2"
val symbol_name = "seed_scalar"
val output_path = "{path}"
val module = rt_cranelift_new_aot_module(rt_string_data(module_name), module_name.len(), 0)
val data = rt_cranelift_declare_global_data_v2(module, rt_string_data(symbol_name), symbol_name.len(), 4, 29, 0, 16)
val emitted = rt_cranelift_emit_object_raw(module, rt_string_data(output_path), output_path.len())
rt_cranelift_free_module(module)
main = if module != 0 and data != 0 and emitted: 0 else: 1
"#);
    let module = Parser::new(&source).parse().unwrap();
    assert_eq!(interpreter::evaluate_module(&module.items).unwrap(), 0);
    let bytes = std::fs::read(output).unwrap();
    let object = object::File::parse(bytes.as_slice()).unwrap();
    let symbol = object.symbol_by_name("seed_scalar").expect("declared native symbol");
    assert!(symbol.is_global());
    assert_eq!(symbol.size(), 8);
    let section = object.section_by_index(symbol.section_index().unwrap()).unwrap();
    assert!(section.align() >= 16);
    let offset = (symbol.address() - section.address()) as usize;
    assert_eq!(&section.data().unwrap()[offset..offset + 8], &29_i64.to_le_bytes());
}
