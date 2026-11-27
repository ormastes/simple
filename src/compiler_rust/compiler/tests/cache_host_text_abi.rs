//! Execute the seed's actual call lowering against cache-host C ABI providers.
//! A valid directory alone did not prevent the old seed from passing a boxed
//! string as the path and omitting its length, breaking --emit-entry-object.

use cranelift_codegen::{
    ir::{types, AbiParam, InstBuilder},
    settings,
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};
use simple_compiler::codegen::{
    instr::{calls, InstrContext},
    runtime_sffi,
};
use simple_compiler::mir::{CallTarget, VReg};
use simple_runtime::value::{rt_string_data, rt_string_len, rt_string_new};
use std::collections::HashMap;

fn text(value: &str) -> i64 {
    rt_string_new(value.as_ptr(), value.len() as u64).to_raw() as i64
}

fn generated_call(name: &str, provider: *const u8, arguments: &[i64]) -> i64 {
    let isa = cranelift_native::builder()
        .expect("host ISA")
        .finish(settings::Flags::new(settings::builder()))
        .expect("ISA flags");
    let mut jit = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
    jit.symbol(name, provider);
    jit.symbol("rt_string_data", rt_string_data as *const u8);
    jit.symbol("rt_string_len", rt_string_len as *const u8);
    let mut module = JITModule::new(jit);
    let mut imports = HashMap::new();
    for symbol in [name, "rt_string_data", "rt_string_len"] {
        let spec = runtime_sffi::spec_for(symbol).expect("registered machine signature");
        let signature = spec.build_signature(module.make_signature().call_conv);
        imports.insert(
            symbol.to_owned(),
            module.declare_function(symbol, Linkage::Import, &signature).unwrap(),
        );
    }
    let mut context = module.make_context();
    context.func.signature = module.make_signature();
    context.func.signature.returns.push(AbiParam::new(types::I64));
    let entry = module
        .declare_function("cache_host_abi_probe", Linkage::Export, &context.func.signature)
        .unwrap();
    let mut frontend = FunctionBuilderContext::new();
    {
        let mut builder = FunctionBuilder::new(&mut context.func, &mut frontend);
        let block = builder.create_block();
        builder.switch_to_block(block);
        builder.seal_block(block);
        let mut ctx = InstrContext::new_for_test(&mut module, &imports);
        let args: Vec<_> = arguments
            .iter()
            .enumerate()
            .map(|(index, argument)| {
                let register = VReg(index as u32);
                ctx.vreg_values
                    .insert(register, builder.ins().iconst(types::I64, *argument));
                register
            })
            .collect();
        let result = VReg(arguments.len() as u32);
        calls::compile_call(
            &mut ctx,
            &mut builder,
            &Some(result),
            &CallTarget::Fs(name.to_owned()),
            &args,
        )
        .expect("lower the real runtime call");
        builder.ins().return_(&[ctx.vreg_values[&result]]);
        builder.finalize();
    }
    module.define_function(entry, &mut context).unwrap();
    module.finalize_definitions().unwrap();
    let compiled: extern "C" fn() -> i64 = unsafe { std::mem::transmute(module.get_finalized_function(entry)) };
    compiled()
}

#[test]
fn cache_host_text_family_machine_arity() {
    let cases: &[(&str, &[usize], usize)] = &[
        ("rt_cache_host_open_root_v1", &[0], 2),
        ("rt_cache_host_open_read_v1", &[1], 3),
        ("rt_cache_host_open_child_v1", &[1], 4),
        ("rt_cache_host_open_cas_kind_v1", &[1], 4),
        ("rt_cache_host_open_cas_shard_v1", &[1], 5),
        ("rt_cache_host_open_cas_leaf_v1", &[1], 3),
        ("rt_cache_host_open_pinned_cas_v1", &[1, 2], 6),
        ("rt_cache_host_publish_noreplace_v1", &[1], 3),
        ("rt_cache_host_publish_retained_noreplace_v2", &[1], 3),
        ("rt_cache_host_quarantine_v1", &[2], 4),
    ];
    for &(name, text_indices, machine_arity) in cases {
        assert_eq!(calls::text_arg_indices(name), Some(text_indices), "{name}");
        let spec = runtime_sffi::spec_for(name).expect(name);
        assert_eq!(spec.params.len(), machine_arity, "{name}");
        assert_eq!(spec.returns, &[types::I64], "{name}");
    }
    assert_eq!(calls::text_arg_indices("rt_cache_host_close_v1"), None);
}

#[cfg(unix)]
#[test]
fn cache_host_generated_calls_open_real_root_child_and_object() {
    use simple_runtime::cache_host_authority_v1::*;
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().to_str().unwrap();
    let root = generated_call(
        "rt_cache_host_open_root_v1",
        rt_cache_host_open_root_v1 as *const u8,
        &[text(path)],
    );
    assert!(
        root > 0,
        "generated root call must deliver actual path bytes and length"
    );
    let child = generated_call(
        "rt_cache_host_open_child_v1",
        rt_cache_host_open_child_v1 as *const u8,
        &[root, text("spool"), 1],
    );
    assert!(
        child > 0,
        "create must remain after the expanded name pointer and length"
    );
    assert!(directory.path().join("spool").is_dir());
    std::fs::write(directory.path().join("spool/object"), b"abi-proof").unwrap();
    let object = generated_call(
        "rt_cache_host_open_read_v1",
        rt_cache_host_open_read_v1 as *const u8,
        &[child, text("object")],
    );
    assert!(object > 0, "generated open-read must preserve its authority argument");
    assert_eq!(unsafe { rt_cache_host_size_v1(object, 100) }, 9);
    unsafe {
        rt_cache_host_close_v1(object);
        rt_cache_host_close_v1(child);
        rt_cache_host_close_v1(root);
    }
}

#[test]
fn cache_host_generated_two_text_call_preserves_trailing_scalar() {
    extern "C" fn capture(
        pin: i64,
        kind: *const u8,
        kind_len: i64,
        digest: *const u8,
        digest_len: i64,
        now: i64,
    ) -> i64 {
        if pin != 17 || kind_len != 3 || digest_len != 64 || now != 29 {
            return 0;
        }
        let kind = unsafe { std::slice::from_raw_parts(kind, 3) };
        let digest = unsafe { std::slice::from_raw_parts(digest, 64) };
        i64::from(kind == b"aot" && digest == b"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef")
    }
    assert_eq!(
        generated_call(
            "rt_cache_host_open_pinned_cas_v1",
            capture as *const u8,
            &[
                17,
                text("aot"),
                text("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"),
                29
            ]
        ),
        1
    );
}
