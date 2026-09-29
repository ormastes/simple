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
    extern "C" fn grow_fallback(_array: i64, _value: i64) -> i64 {
        // Grow-path fallback for fast-path push tests: never invoked (the
        // fixtures always have spare capacity), only linked. Returns the
        // FAM-ABI shape (a header-sized word), matching the I64 return the
        // push-family imports carry when fam_arrays is set.
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
        // Mirror runtime_funcs_for_target: the FAM freestanding push family
        // returns the possibly moved header (I64); everything else keeps the
        // canonical bool (I8) return.
        sig.returns.push(cranelift_codegen::ir::AbiParam::new(if fam_arrays {
            types::I64
        } else {
            types::I8
        }));
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
        },
    );
    // FAM push-return ABI: dest is the array VALUE, not a bool success flag.
    // The in-capacity store never moves the header, so the handle is unchanged.
    assert_eq!(fam(arr.tagged_ptr), arr.tagged_ptr);
    // len bumped to 4 in the u32 field, cap untouched at 8.
    assert_eq!(arr.storage[1] & 0xFFFF_FFFF, 4);
    assert_eq!(arr.storage[1] >> 32, 8);
    // items[3] = ENCODE_INT(0xDEAD & 0xFFFFFFFF).
    assert_eq!(arr.storage[2 + 3], (0xDEADu64) << 3);
}

// ---------------------------------------------------------------------------
// Freestanding-shaped push-grow regression (bump allocator ALWAYS moves).
//
// Evidence: doc/08_tracking/bug/array_push_stale_receiver_store_arm64_2026-09-25.md
// — on the aarch64 guest, `alloc_zeroed_bytes(115209168)` push loop leaked one
// 16,400-byte block per push from element 1025 on: the compiled loop kept
// re-pushing the stale pre-grow array value because rt_array_push's return
// (the relocated header) was discarded. The bump-allocator fixture below
// reproduces that runtime shape exactly: realloc NEVER extends in place, so
// every grow relocates the header, and the push returns the NEW header.
// ---------------------------------------------------------------------------

/// Moving bump-allocator FAM runtime mirroring
/// examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c.
/// GROWS/ALLOCS pin the exact allocation behavior: the stale-receiver defect
/// re-grows the pre-grow block once PER PUSH instead of once per doubling.
mod fam_bump {
    use std::alloc::{alloc, Layout};
    use std::sync::atomic::{AtomicUsize, Ordering};

    pub static GROWS: AtomicUsize = AtomicUsize::new(0);
    pub static ALLOCS: AtomicUsize = AtomicUsize::new(0);

    const HDR: usize = 2; // {u32 type|u32 size, u32 len|u32 cap}

    fn layout(cap: usize) -> Layout {
        Layout::from_size_align((HDR + cap) * 8, 8).unwrap()
    }

    unsafe fn len_cap(p: *mut u64) -> (usize, usize) {
        let w = *p.add(1);
        ((w & 0xFFFF_FFFF) as usize, (w >> 32) as usize)
    }

    unsafe fn set_len(p: *mut u64, len: usize, cap: usize) {
        *p.add(1) = (len as u64) | ((cap as u64) << 32);
    }

    /// FAM rt_array_new: cap clamped to the 64-element minimum like the
    /// freestanding stub.
    pub extern "C" fn rt_array_new(cap_val: i64) -> i64 {
        let cap = if cap_val < 64 { 64 } else { cap_val as usize };
        unsafe {
            let p = alloc(layout(cap)) as *mut u64;
            *p = 2u64 | (((16 + cap * 8) as u64) << 32); // HEAP_ARRAY = 2
            set_len(p, 0, cap);
            for i in 0..cap {
                *p.add(HDR + i) = 3; // tagged nil
            }
            ALLOCS.fetch_add(1, Ordering::SeqCst);
            (p as i64) | 1
        }
    }

    /// FAM rt_byte_array_new: on the FAM layout byte arrays are ordinary
    /// tagged-slot arrays (the aarch64/arm32 stubs forward to rt_array_new).
    pub extern "C" fn rt_byte_array_new(cap_val: i64) -> i64 {
        rt_array_new(cap_val)
    }

    /// FAM rt_array_push: bump realloc ALWAYS moves; returns the new header.
    pub extern "C" fn rt_array_push(arr: i64, val: i64) -> i64 {
        unsafe {
            let mut p = (arr & !7) as *mut u64;
            let (len, cap) = len_cap(p);
            if len >= cap {
                GROWS.fetch_add(1, Ordering::SeqCst);
                ALLOCS.fetch_add(1, Ordering::SeqCst);
                let new_cap = cap * 2;
                let np = alloc(layout(new_cap)) as *mut u64;
                for i in 0..len {
                    *np.add(HDR + i) = *p.add(HDR + i);
                }
                for i in len..new_cap {
                    *np.add(HDR + i) = 3;
                }
                *np = 2u64 | (((16 + new_cap * 8) as u64) << 32);
                set_len(np, len, new_cap);
                p = np;
            }
            let (len, cap) = len_cap(p);
            *p.add(HDR + len) = val as u64;
            set_len(p, len + 1, cap);
            (p as i64) | 1
        }
    }

    /// FAM rt_typed_bytes_u8_push: forward to rt_array_push with the tagged
    /// byte slot (ENCODE_INT(byte) = byte << 3, TAG_INT = 0).
    pub extern "C" fn rt_typed_bytes_u8_push(arr: i64, val: i64) -> i64 {
        rt_array_push(arr, (val & 0xFF) << 3)
    }
}

/// Lower `source` with the FAM push-return ABI, compile it for an
/// `aarch64-unknown-none` target (fam_arrays inline accessors, I64-returning
/// push imports), and execute `entry` against the moving bump-allocator
/// runtime above. Returns the entry function's i64 result.
fn jit_fam_module(source: &str, entry: &str) -> i64 {
    use crate::codegen::common_backend::CodegenBackend;
    use simple_common::target::{Target, TargetArch, TargetOS};
    use simple_native_loader::RuntimeSymbolProvider;

    let mut parser = simple_parser::Parser::new(source);
    let ast = parser.parse().expect("parse fixture");
    let hir = crate::hir::lower(&ast).expect("hir lower fixture");
    let mir = crate::mir::MirLowerer::new()
        .with_refined_types(&hir.refined_types)
        .with_type_registry(&hir.types)
        .with_trait_infos(&hir.trait_infos)
        .with_array_push_returns_header(true)
        .lower_module(&hir)
        .expect("mir lower fixture");

    let isa_builder = cranelift_native::builder().expect("host ISA");
    let flags = settings::Flags::new(settings::builder());
    let isa = isa_builder.finish(flags).expect("ISA");
    let mut jit_builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
    let provider = simple_native_loader::static_provider();
    for &name in simple_native_loader::RUNTIME_SYMBOL_NAMES {
        if let Some(ptr) = provider.get_symbol(name) {
            jit_builder.symbol(name, ptr);
        }
    }
    // Override the array constructor/push family with the moving FAM twins.
    jit_builder.symbol("rt_array_new", fam_bump::rt_array_new as usize as *const u8);
    jit_builder.symbol("rt_byte_array_new", fam_bump::rt_byte_array_new as usize as *const u8);
    jit_builder.symbol("rt_array_push", fam_bump::rt_array_push as usize as *const u8);
    jit_builder.symbol(
        "rt_typed_bytes_u8_push",
        fam_bump::rt_typed_bytes_u8_push as usize as *const u8,
    );
    let module = JITModule::new(jit_builder);

    let target = Target::new(TargetArch::Aarch64, TargetOS::None);
    let mut backend = CodegenBackend::with_module_and_target(module, target).expect("backend");
    backend.compile_all_functions(&mir).expect("compile fixture");
    backend.module.finalize_definitions().expect("finalize");
    if let Some(&init_id) = backend.func_ids.get("__module_init") {
        let init_ptr = backend.module.get_finalized_function(init_id);
        let init: extern "C" fn() = unsafe { std::mem::transmute(init_ptr) };
        init();
    }
    let func_id = backend.func_ids[entry];
    let ptr = backend.module.get_finalized_function(func_id);
    let f: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    f()
}

/// The exact Wall-7 shape: a fused `arr = arr.push(x)` loop pushing far past
/// the created capacity on a heap whose realloc ALWAYS moves. Must end with
/// len == N and correct contents, with exactly one allocation per doubling
/// (6 grows for 3000 elements from the 64-element minimum capacity).
#[test]
fn fam_grow_loop_fused_push_survives_moving_realloc() {
    use std::sync::atomic::Ordering;
    fam_bump::GROWS.store(0, Ordering::SeqCst);
    fam_bump::ALLOCS.store(0, Ordering::SeqCst);
    let rc = jit_fam_module(
        "fn grow_loop() -> i64:\n    var arr: [i64] = []\n    var i: i64 = 0\n    while i < 3000:\n        arr = arr.push(i)\n        i = i + 1\n    if arr.len() != 3000:\n        return -1\n    if arr[0] != 0:\n        return -2\n    if arr[1023] != 1023:\n        return -3\n    if arr[2999] != 2999:\n        return -4\n    return 0\n",
        "grow_loop",
    );
    assert_eq!(rc, 0, "grow loop must end with len=3000 and correct contents");
    assert_eq!(
        fam_bump::GROWS.load(Ordering::SeqCst),
        6,
        "exactly one grow per capacity doubling (64->128->256->512->1024->2048)"
    );
    assert_eq!(fam_bump::ALLOCS.load(Ordering::SeqCst), 7, "one new + six grows");
}

/// Statement-position `arr.push(x)` (no assignment): the store-back into the
/// receiver local is the only thing that keeps the loop-carried value
/// advancing across grows.
#[test]
fn fam_grow_loop_statement_push_survives_moving_realloc() {
    use std::sync::atomic::Ordering;
    fam_bump::GROWS.store(0, Ordering::SeqCst);
    fam_bump::ALLOCS.store(0, Ordering::SeqCst);
    let len = jit_fam_module(
        "fn grow_loop_stmt() -> i64:\n    var arr: [i64] = []\n    var i: i64 = 0\n    while i < 3000:\n        arr.push(i)\n        i = i + 1\n    return arr.len()\n",
        "grow_loop_stmt",
    );
    assert_eq!(len, 3000, "statement push loop must keep the receiver advanced");
    assert_eq!(fam_bump::GROWS.load(Ordering::SeqCst), 6);
    assert_eq!(fam_bump::ALLOCS.load(Ordering::SeqCst), 7);
}

/// Typed [u8] statement push through the inline fast path: in-capacity pushes
/// store inline; the grow call must still rebind the receiver local.
#[test]
fn fam_grow_loop_typed_u8_push_survives_moving_realloc() {
    use std::sync::atomic::Ordering;
    fam_bump::GROWS.store(0, Ordering::SeqCst);
    fam_bump::ALLOCS.store(0, Ordering::SeqCst);
    let len = jit_fam_module(
        "fn grow_loop_u8() -> i64:\n    var arr: [u8] = []\n    var i: i64 = 0\n    while i < 3000:\n        arr.push(i as u8)\n        i = i + 1\n    return arr.len()\n",
        "grow_loop_u8",
    );
    // The empty [u8] literal starts at the codec-table capacity 1024.
    assert_eq!(len, 3000, "typed u8 push loop must keep the receiver advanced");
    assert_eq!(fam_bump::GROWS.load(Ordering::SeqCst), 2, "grows at 1024 and 2048");
}

/// Module-init `[0; N]` fill loop on the FAM target: the compact zero-fill
/// push loop must still produce a real length-N array handle (the loop
/// restructure that threads the push return must not break the no-grow case),
/// and the global store must publish the post-fill handle.
#[test]
fn fam_module_init_zero_fill_loop_produces_len_n_array() {
    use std::sync::atomic::Ordering;
    fam_bump::GROWS.store(0, Ordering::SeqCst);
    fam_bump::ALLOCS.store(0, Ordering::SeqCst);
    let rc = jit_fam_module(
        "var big: [i64; 1000] = [0; 1000]\n\nfn read_big() -> i64:\n    if big.len() != 1000:\n        return -1\n    if big[0] != 0:\n        return -2\n    if big[999] != 0:\n        return -3\n    return 0\n",
        "read_big",
    );
    assert_eq!(rc, 0, "module-init [0; N] fill must yield a length-N zero array");
    assert_eq!(fam_bump::GROWS.load(Ordering::SeqCst), 0, "cap == count: no grow expected");
    assert_eq!(fam_bump::ALLOCS.load(Ordering::SeqCst), 1, "exactly the constructor allocation");
}
