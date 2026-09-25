//! Regression tests for the freestanding FAM RuntimeArray ABI in the seed
//! compiler's inline array accessors.
//!
//! Evidence: doc/08_tracking/aarch64_in_guest_clang_compile_lane_status_2026-09-25.md
//! (Blocker 2) — on an `aarch64-unknown-none` kernel built by the seed compiler,
//! `.len()` on a sector buffer returned 2199023256064 (512<<32|512) and
//! `arr[i]` returned 0, because the inline accessors hardcoded the hosted
//! layout (`u64 len@8; u64 cap@16; RuntimeValue *data@24`) while the
//! aarch64/arm32/x86_32 freestanding C runtimes implement
//! `{u32 len@8; u32 cap@12; RuntimeValue items@16}` with tagged slots.
//!
//! Each test JIT-builds a tiny function through the REAL inline path with
//! `fam_arrays = true` and executes it against a FAM-layout array allocated
//! in the test — the hosted (`fam_arrays = false`) twin is executed against
//! the same object to pin the exact divergence.

use super::*;
use cranelift_codegen::ir::types;
use cranelift_codegen::settings;
use cranelift_codegen::ir::InstBuilder;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};

/// FAM RuntimeArray fixture matching the freestanding C ABI of
/// examples/09_embedded/simple_os/arch/{arm64,arm32,x86_32}/boot/baremetal_stubs.c:
/// `{u32 type=HEAP_ARRAY, u32 size, u32 len, u32 cap, RuntimeValue items[]}`,
/// every element stored as ENCODE_INT(byte) = byte << 3 (TAG_INT = 0).
struct FamArray {
    storage: Vec<u64>,
    tagged_ptr: i64,
}

fn fam_array(bytes: &[u8]) -> FamArray {
    let len = bytes.len();
    let size = 16 + 8 * len;
    let mut storage = Vec::with_capacity(2 + len);
    storage.push(2u64 | ((size as u64) << 32)); // hdr {type=HEAP_ARRAY, size}
    storage.push((len as u64) | ((len as u64) << 32)); // u32 len | u32 cap
    for &b in bytes {
        storage.push((b as u64) << 3);
    }
    let tagged_ptr = (storage.as_ptr() as i64) | 1; // TAG_HEAP = 1
    FamArray { storage, tagged_ptr }
}

/// JIT-compile `name(array) -> i64` whose body is built by `build`, with the
/// given fam_arrays flag, and return the executable pointer + module (which
/// must stay alive for the pointer to remain valid).
fn jit_array_fn(
    name: &str,
    fam_arrays: bool,
    runtime_names: &[&str],
    build: impl FnOnce(&mut InstrContext<'_, JITModule>, &mut FunctionBuilder, VReg),
) -> (JITModule, extern "C" fn(i64) -> i64) {
    extern "C" fn grow_fallback(_array: i64, _value: i64) -> u8 {
        // Grow-path fallback for fast-path push tests: never invoked (the
        // fixtures always have spare capacity), only linked.
        1
    }
    let isa_builder = cranelift_native::builder().expect("host ISA");
    let flags = settings::Flags::new(settings::builder());
    let isa = isa_builder.finish(flags).expect("ISA");
    let mut jit_builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
    // JITModule resolves every import at finalize time even if the fast path
    // never calls it — give the grow fallback a dummy address.
    jit_builder.symbol("rt_typed_words_u32_push", grow_fallback as usize as *const u8);
    let mut module = JITModule::new(jit_builder);

    let mut runtime_funcs_by_string = std::collections::HashMap::new();
    for rt in runtime_names {
        let mut sig = module.make_signature();
        sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
        sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
        sig.returns.push(cranelift_codegen::ir::AbiParam::new(types::I8));
        let id = module
            .declare_function(rt, Linkage::Import, &sig)
            .expect("declare runtime import");
        runtime_funcs_by_string.insert(rt.to_string(), id);
    }

    let mut fn_sig = module.make_signature();
    fn_sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
    fn_sig.returns.push(cranelift_codegen::ir::AbiParam::new(types::I64));
    let fn_id = module
        .declare_function(name, Linkage::Export, &fn_sig)
        .expect("declare test fn");

    let mut ctx = module.make_context();
    ctx.func.signature = fn_sig;
    let mut fn_ctx = FunctionBuilderContext::new();
    let result = {
        let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fn_ctx);
        let entry = fb.create_block();
        fb.append_block_param(entry, types::I64);
        fb.switch_to_block(entry);
        fb.seal_block(entry);
        let array_param = fb.block_params(entry)[0];

        let mut instr_ctx = InstrContext::new_for_test(&mut module, &runtime_funcs_by_string);
        instr_ctx.fam_arrays = fam_arrays;

        let array_vreg = VReg(1000);
        instr_ctx.vreg_values.insert(array_vreg, array_param);
        build(&mut instr_ctx, &mut fb, array_vreg);

        // The inline builders leave the cursor on their done block with the
        // result stored in vreg 2000.
        let out = *instr_ctx.vreg_values.get(&VReg(2000)).expect("result vreg");
        fb.ins().return_(&[out]);
        fb.finalize();
        out
    };
    let _ = result;

    module.define_function(fn_id, &mut ctx).expect("define function");
    module.finalize_definitions().expect("finalize definitions");
    let ptr = module.get_finalized_function(fn_id);
    let f: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(ptr) };
    (module, f)
}

/// JIT-compile `name(array, index) -> i64` (two i64 params).
fn jit_array_index_fn(
    name: &str,
    fam_arrays: bool,
    index_ty: Option<TypeId>,
    build: impl FnOnce(&mut InstrContext<'_, JITModule>, &mut FunctionBuilder, VReg, VReg),
) -> (JITModule, extern "C" fn(i64, i64) -> i64) {
    let isa_builder = cranelift_native::builder().expect("host ISA");
    let flags = settings::Flags::new(settings::builder());
    let isa = isa_builder.finish(flags).expect("ISA");
    let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
    let mut module = JITModule::new(builder);

    let mut fn_sig = module.make_signature();
    fn_sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
    fn_sig.params.push(cranelift_codegen::ir::AbiParam::new(types::I64));
    fn_sig.returns.push(cranelift_codegen::ir::AbiParam::new(types::I64));
    let fn_id = module
        .declare_function(name, Linkage::Export, &fn_sig)
        .expect("declare test fn");

    let mut ctx = module.make_context();
    ctx.func.signature = fn_sig;
    let mut fn_ctx = FunctionBuilderContext::new();
    {
        let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fn_ctx);
        let entry = fb.create_block();
        fb.append_block_param(entry, types::I64);
        fb.append_block_param(entry, types::I64);
        fb.switch_to_block(entry);
        fb.seal_block(entry);
        let (array_param, index_param) = {
            let ps = fb.block_params(entry);
            (ps[0], ps[1])
        };

        let mut instr_ctx = InstrContext::new_for_test(&mut module, &std::collections::HashMap::new());
        instr_ctx.fam_arrays = fam_arrays;

        let array_vreg = VReg(1000);
        let index_vreg = VReg(1001);
        instr_ctx.vreg_values.insert(array_vreg, array_param);
        instr_ctx.vreg_values.insert(index_vreg, index_param);
        if let Some(ty) = index_ty {
            instr_ctx.vreg_types.insert(index_vreg, ty);
        }
        build(&mut instr_ctx, &mut fb, array_vreg, index_vreg);

        let out = *instr_ctx.vreg_values.get(&VReg(2000)).expect("result vreg");
        fb.ins().return_(&[out]);
        fb.finalize();
    }

    module.define_function(fn_id, &mut ctx).expect("define function");
    module.finalize_definitions().expect("finalize definitions");
    let ptr = module.get_finalized_function(fn_id);
    let f: extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(ptr) };
    (module, f)
}

/// The exact Blocker-2 repro: a 512-element FAM array `{len=512, cap=512}`.
fn sector_array() -> FamArray {
    let mut bytes = Vec::with_capacity(512);
    bytes.push(0xEB); // FAT32 jump instruction byte 0
    bytes.push(0x58); // byte 1 — the values seen in the serial evidence
    for i in 2..512 {
        bytes.push((i & 0xFF) as u8);
    }
    fam_array(&bytes)
}

#[test]
fn fam_array_len_reads_u32_len_field() {
    let arr = sector_array();

    // Hosted-layout inline (fam_arrays = false) reads i64@8 across the FAM
    // {u32 len, u32 cap} pair — this is the exact 512<<32|512 miscompile
    // reported from the aarch64 guest.
    let (_m, hosted) = jit_array_fn("hosted_len", false, &[], |ctx, fb, a| {
        let v = super::super::helpers::inline_runtime_array_len_value(fb, ctx.vreg_values[&a], false);
        ctx.vreg_values.insert(VReg(2000), v);
    });
    assert_eq!(hosted(arr.tagged_ptr), (512i64 << 32) | 512);

    // FAM inline must read only the u32 len field.
    let (_m, fam) = jit_array_fn("fam_len", true, &[], |ctx, fb, a| {
        let v = super::super::helpers::inline_runtime_array_len_value(fb, ctx.vreg_values[&a], true);
        ctx.vreg_values.insert(VReg(2000), v);
    });
    assert_eq!(fam(arr.tagged_ptr), 512);
}

#[test]
fn fam_generic_rt_len_array_arm_uses_u32_and_string_arm_keeps_u64() {
    use super::super::helpers::inline_runtime_len_value;
    let arr = sector_array();

    // Generic rt_len on the FAM array (baremetal tag vocabulary, fam layout).
    let (_m, fam) = jit_array_fn("fam_rt_len", true, &[], |ctx, fb, a| {
        let v = inline_runtime_len_value(fb, ctx.vreg_values[&a], true, true);
        ctx.vreg_values.insert(VReg(2000), v);
    });
    assert_eq!(fam(arr.tagged_ptr), 512);

    // RuntimeString in the FAM C ABI keeps u64 len@8 — the string arm must
    // NOT be narrowed to u32.
    let mut string_storage: Vec<u64> = vec![1, 7]; // type=HEAP_STRING, u64 len=7
    let str_ptr = (string_storage.as_ptr() as i64) | 1;
    let (_m2, fam_str) = jit_array_fn("fam_rt_len_str", true, &[], |ctx, fb, a| {
        let v = inline_runtime_len_value(fb, ctx.vreg_values[&a], true, true);
        ctx.vreg_values.insert(VReg(2000), v);
    });
    assert_eq!(fam_str(str_ptr), 7);
    let _ = &mut string_storage;
}

#[test]
fn fam_bytes_u8_at_decodes_tagged_slot() {
    let arr = sector_array();

    let (_m, fam) = jit_array_index_fn("fam_byte_at", true, None, |ctx, fb, a, i| {
        let dest = VReg(2000);
        assert!(compile_inline_bytes_u8_at(ctx, fb, &Some(dest), &[a, i], true).expect("inline"));
    });
    assert_eq!(fam(arr.tagged_ptr, 0), 0xEB);
    assert_eq!(fam(arr.tagged_ptr, 1), 0x58);
    assert_eq!(fam(arr.tagged_ptr, 511), 255);
    // Out of bounds reads return 0 (not a wild read).
    assert_eq!(fam(arr.tagged_ptr, 512), 0);
    // Negative index addresses from the end.
    assert_eq!(fam(arr.tagged_ptr, -1), 255);
}

#[test]
fn fam_array_get_returns_tagged_slot() {
    let arr = sector_array();

    let (_m, fam) = jit_array_index_fn("fam_get", true, None, |ctx, fb, a, i| {
        let dest = VReg(2000);
        assert!(compile_inline_array_get(ctx, fb, &Some(dest), &[a, i]).expect("inline"));
    });
    // items[0] = ENCODE_INT(0xEB) = 0xEB << 3.
    assert_eq!(fam(arr.tagged_ptr, 0), 0xEBi64 << 3);
    // Out of bounds returns tagged nil (3).
    assert_eq!(fam(arr.tagged_ptr, 512), 3);
}

#[test]
fn fam_array_set_writes_slot_as_is() {
    let arr = sector_array();

    let (_m, fam) = jit_array_index_fn("fam_set", true, None, |ctx, fb, a, i| {
        // value vreg = 1002. rt_array_set stores the value AS a RuntimeValue
        // (callers pass already-tagged values, matching the C rt_array_set).
        let dest = VReg(2000);
        let value = VReg(1002);
        let v = fb.ins().iconst(types::I64, 0xAB << 3);
        ctx.vreg_values.insert(value, v);
        assert!(compile_inline_array_set(ctx, fb, &Some(dest), &[a, i, value]).expect("inline"));
        // done_block carries the i64 success flag directly.
    });
    assert_eq!(fam(arr.tagged_ptr, 5), 1);
    // items[5] must now hold the tagged value verbatim.
    assert_eq!(arr.storage[2 + 5], 0xABu64 << 3);
}

#[test]
fn fam_typed_bytes_u32_le_composes_from_slots() {
    let bytes = [0x21u8, 0x03, 0x00, 0x00, 0xFF, 0x10, 0xAA, 0x55];
    let arr = fam_array(&bytes);

    let (_m, fam32) = jit_array_index_fn("fam_u32_le", true, None, |ctx, fb, a, i| {
        let dest = VReg(2000);
        assert!(
            compile_inline_typed_bytes_le_unchecked(ctx, fb, &Some(dest), &[a, i], 4).expect("inline")
        );
    });
    assert_eq!(fam32(arr.tagged_ptr, 0), 0x00000321);
    assert_eq!(fam32(arr.tagged_ptr, 4), 0x55AA10FFu32 as i64);

    let (_m2, fam1) = jit_array_index_fn("fam_u8_unchecked", true, None, |ctx, fb, a, i| {
        let dest = VReg(2000);
        assert!(
            compile_inline_typed_bytes_le_unchecked(ctx, fb, &Some(dest), &[a, i], 1).expect("inline")
        );
    });
    assert_eq!(fam1(arr.tagged_ptr, 4), 0xFF);
}

#[test]
fn fam_array_data_ptr_is_items_base_header_plus_16() {
    let arr = sector_array();

    let (_m, fam) = jit_array_fn("fam_data_ptr", true, &[], |ctx, fb, a| {
        let dest = VReg(2000);
        assert!(compile_inline_array_data_ptr(ctx, fb, &Some(dest), &[a]).expect("inline"));
    });
    let raw = arr.storage.as_ptr() as i64;
    assert_eq!(fam(arr.tagged_ptr), raw + 16);
}

#[test]
fn fam_typed_words_push_appends_slot_and_bumps_u32_len() {
    // len = 3, cap = 8 (spare capacity so the fast path stores inline).
    let mut storage: Vec<u64> = vec![0; 2 + 8];
    storage[0] = 2 | (((16 + 8 * 8) as u64) << 32);
    storage[1] = 3 | (8u64 << 32);
    let arr = FamArray {
        tagged_ptr: (storage.as_ptr() as i64) | 1,
        storage,
    };

    let (_m, fam) = jit_array_fn(
        "fam_words_push",
        true,
        &["rt_typed_words_u32_push"],
        |ctx, fb, a| {
            let dest = VReg(2000);
            let value = VReg(1002);
            let v = fb.ins().iconst(types::I64, 0xDEAD);
            ctx.vreg_values.insert(value, v);
            assert!(compile_inline_typed_words_push(ctx, fb, &Some(dest), &[a, value], 4).expect("inline"));
            let flag = ctx.vreg_values[&dest];
            let widened = fb.ins().uextend(types::I64, flag);
            ctx.vreg_values.insert(dest, widened);
        },
    );
    assert_eq!(fam(arr.tagged_ptr), 1);
    // len bumped to 4 in the u32 field, cap untouched at 8.
    assert_eq!(arr.storage[1] & 0xFFFF_FFFF, 4);
    assert_eq!(arr.storage[1] >> 32, 8);
    // items[3] = ENCODE_INT(0xDEAD & 0xFFFFFFFF).
    assert_eq!(arr.storage[2 + 3], (0xDEADu64) << 3);
}
