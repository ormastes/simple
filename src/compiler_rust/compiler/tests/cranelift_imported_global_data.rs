//! Direct provider ABI regression; this does not execute the Rust interpreter.
use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget};
use simple_compiler::codegen::cranelift_sffi::*;

#[test]
fn imported_global_emits_reference_without_definition() {
    let dir = tempfile::tempdir().unwrap();
    let name = "shared_static";
    let owner_path = dir.path().join("owner.o");
    let consumer_path = dir.path().join("consumer.o");
    unsafe {
        // Target 0 is x86_64 AOT; object verification is host-independent.
        let owner = rt_cranelift_new_aot_module("owner".as_ptr() as i64, 5, 0);
        assert!(owner > 0);
        let defined = rt_cranelift_declare_global_data_v2(
            owner, name.as_ptr() as i64, name.len() as i64, 4, 29, 0, 16);
        assert!(defined > 0);
        let path = owner_path.to_str().unwrap();
        assert!(rt_cranelift_emit_object_raw(owner, path.as_ptr() as i64, path.len() as i64));
        rt_cranelift_free_module(owner);

        let consumer = rt_cranelift_new_aot_module("consumer".as_ptr() as i64, 8, 0);
        assert!(consumer > 0);
        // An import must not silently ignore an attempted initializer.
        assert_eq!(rt_cranelift_declare_global_data_v2(
            consumer, name.as_ptr() as i64, name.len() as i64, 4, 29, 1, 8), 0);
        let imported = rt_cranelift_declare_global_data_v2(
            consumer, name.as_ptr() as i64, name.len() as i64, 4, 0, 1, 8);
        assert!(imported > 0);
        let signature = rt_cranelift_new_signature(0);
        rt_cranelift_sig_set_return(signature, 4);
        let reader = "read_shared_static";
        let ctx = rt_cranelift_begin_function(
            consumer, reader.as_ptr() as i64, reader.len() as i64, signature);
        assert!(ctx > 0);
        let block = rt_cranelift_create_block(ctx);
        rt_cranelift_switch_to_block(ctx, block);
        rt_cranelift_seal_block(ctx, block);
        let addr = rt_cranelift_data_addr_in_func(ctx, imported);
        assert!(addr > 0);
        let value = rt_cranelift_load(ctx, 4, addr, 0);
        assert!(value > 0);
        rt_cranelift_return(ctx, value);
        let function = rt_cranelift_end_function(ctx);
        assert!(function > 0);
        assert!(rt_cranelift_aot_define_function(
            consumer, reader.as_ptr() as i64, reader.len() as i64, function));
        let path = consumer_path.to_str().unwrap();
        assert!(rt_cranelift_emit_object_raw(consumer, path.as_ptr() as i64, path.len() as i64));
        rt_cranelift_free_module(consumer);
    }
    let owner_bytes = std::fs::read(owner_path).unwrap();
    let owner = object::File::parse(owner_bytes.as_slice()).unwrap();
    let definition = owner.symbol_by_name(name).expect("owner symbol");
    assert!(!definition.is_undefined());
    assert!(definition.is_global());
    let section = owner.section_by_index(definition.section_index().unwrap()).unwrap();
    let offset = (definition.address() - section.address()) as usize;
    assert_eq!(&section.data().unwrap()[offset..offset + 8], &29_i64.to_le_bytes());
    assert!(section.align() >= 16);
    let consumer_bytes = std::fs::read(consumer_path).unwrap();
    let consumer = object::File::parse(consumer_bytes.as_slice()).unwrap();
    let reference = consumer.symbol_by_name(name).expect("imported symbol");
    assert!(reference.is_undefined(), "the importer must not define a second slot");
    assert!(consumer.sections().any(|section| section.relocations().any(|(_, relocation)|
        relocation.target() == RelocationTarget::Symbol(reference.index()))));
}
