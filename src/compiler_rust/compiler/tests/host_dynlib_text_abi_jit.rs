//! Cranelift JIT: `rt_host_dynlib_open(path: text, mode)` and
//! `rt_host_dynlib_symbol(handle, name: text)` cross the C ABI as
//! `(ptr, len)` pairs (`runtime/src/value/wsffi_native.rs`). Neither name was in
//! `calls::text_arg_indices`, so the JIT passed the boxed text handle as
//! `path_ptr` and the NEXT argument (`mode`, or nothing) as `path_len`.
//! `raw_text_cstring` refused the length and every JIT `dynlib_open` returned
//! 0 (`loader-failed`), while the interpreter split the text and loaded fine.
//! doc/08_tracking/bug/seed_jit_host_dynlib_open_text_arg_not_split_2026-11-06.md

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

/// Lower one `CallTarget::Fs(name)` through the seed's real call lowering and
/// run it, with `name` bound to `provider`.
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
        .declare_function("host_dynlib_abi_probe", Linkage::Export, &context.func.signature)
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
fn host_dynlib_text_args_are_split_to_ptr_len() {
    assert_eq!(calls::text_arg_indices("rt_host_dynlib_open"), Some(&[0usize][..]));
    assert_eq!(calls::text_arg_indices("rt_host_dynlib_symbol"), Some(&[1usize][..]));
    assert_eq!(calls::text_arg_indices("rt_host_dynlib_close"), None);
    assert_eq!(runtime_sffi::spec_for("rt_host_dynlib_open").unwrap().params.len(), 3);
    assert_eq!(runtime_sffi::spec_for("rt_host_dynlib_symbol").unwrap().params.len(), 3);
}

#[test]
fn host_dynlib_open_receives_path_bytes_length_and_mode() {
    extern "C" fn capture(path: *const u8, path_len: i64, mode: i64) -> i64 {
        if path_len != 12 || mode != 2 {
            return -path_len - 1000 * mode;
        }
        let bytes = unsafe { std::slice::from_raw_parts(path, 12) };
        i64::from(bytes == b"kernel32.dll")
    }
    assert_eq!(
        generated_call("rt_host_dynlib_open", capture as *const u8, &[text("kernel32.dll"), 2]),
        1
    );
}

#[test]
fn host_dynlib_symbol_receives_handle_and_name_bytes() {
    extern "C" fn capture(handle: i64, name: *const u8, name_len: i64) -> i64 {
        if handle != 77 || name_len != 12 {
            return 0;
        }
        let bytes = unsafe { std::slice::from_raw_parts(name, 12) };
        i64::from(bytes == b"GetTickCount")
    }
    assert_eq!(
        generated_call("rt_host_dynlib_symbol", capture as *const u8, &[77, text("GetTickCount")]),
        1
    );
}

/// End to end against the real runtime loader on a library every host has.
#[cfg(any(windows, target_os = "linux"))]
#[test]
fn host_dynlib_generated_calls_load_a_real_library() {
    use simple_runtime::value::{rt_host_dynlib_close, rt_host_dynlib_open, rt_host_dynlib_symbol};
    let (library, symbol) = if cfg!(windows) {
        ("kernel32.dll", "GetTickCount")
    } else {
        ("libc.so.6", "getpid")
    };
    let handle = generated_call(
        "rt_host_dynlib_open",
        rt_host_dynlib_open as *const u8,
        &[text(library), 2],
    );
    assert!(handle > 0, "JIT dynlib open of {library} returned {handle}");
    let address = generated_call(
        "rt_host_dynlib_symbol",
        rt_host_dynlib_symbol as *const u8,
        &[handle, text(symbol)],
    );
    assert!(address > 0, "JIT dynlib symbol {symbol} returned {address}");
    assert_eq!(rt_host_dynlib_close(handle), 0);
}
