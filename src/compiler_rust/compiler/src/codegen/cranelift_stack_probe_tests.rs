use super::*;

fn assert_windows_probe_policy(isa: &dyn cranelift_codegen::isa::TargetIsa) {
    assert!(isa.flags().enable_probestack());
    assert_eq!(isa.flags().probestack_size_log2(), 12);
    assert_eq!(isa.flags().probestack_strategy(), settings::ProbestackStrategy::Inline);
}

#[test]
fn win64_stack_probe_constructor_policy() {
    for target in ["x86_64-pc-windows-msvc", "x86_64-pc-windows-gnu"] {
        let (_, isa) = build_aot_isa_and_triple(target).unwrap();
        assert_windows_probe_policy(isa.as_ref());
        let name = "stack_probe_policy";
        let cpu = "generic";
        for opt in 0..=2 {
            let handle = unsafe { spl_cranelift_new_aot_module_config_v2(
                name.as_ptr() as i64, name.len() as i64,
                target.as_ptr() as i64, target.len() as i64,
                cpu.as_ptr() as i64, cpu.len() as i64, opt, 0, 0,
            ) };
            assert!(handle > 0);
            {
                let modules = AOT_MODULES.lock().unwrap();
                assert_windows_probe_policy(modules[&handle].module.isa());
            }
            unsafe { rt_cranelift_free_module(handle); }
        }
    }
    for target in ["x86_64-unknown-linux-gnu", "x86_64-apple-darwin"] {
        let (_, isa) = build_aot_isa_and_triple(target).unwrap();
        assert!(!isa.flags().enable_probestack(), "non-Windows policy changed: {target}");
    }
}

// Exercise the actual compiler, not a hand-authored prologue. Stores at both
// ends exercise local accesses after the generated frame setup.
fn compile_stack_frame(isa: &dyn cranelift_codegen::isa::TargetIsa, size: u32) -> (Vec<u8>, String) {
    let mut ctx = Context::new();
    ctx.want_disasm = true;
    ctx.func.signature = Signature::new(isa.default_call_conv());
    ctx.func.signature.returns.push(AbiParam::new(types::I32));
    let mut fbctx = FunctionBuilderContext::new();
    let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
    let entry = b.create_block();
    b.switch_to_block(entry);
    b.seal_block(entry);
    let slot = b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, size, 0));
    let value = b.ins().iconst(types::I32, 42);
    b.ins().stack_store(value, slot, 0);
    b.ins().stack_store(value, slot, (size - 4) as i32);
    let first = b.ins().stack_load(types::I32, slot, 0);
    let last = b.ins().stack_load(types::I32, slot, (size - 4) as i32);
    let sum = b.ins().iadd(first, last);
    b.ins().return_(&[sum]);
    b.finalize();
    let code = ctx.compile(isa, &mut Default::default()).unwrap();
    assert!(code.buffer.relocs().is_empty(), "inline probes must not need a runtime libcall");
    (code.buffer.data().to_vec(), code.vcode.clone().unwrap())
}

#[test]
fn win64_stack_probe_generated_frames() {
    let (_, isa) = build_aot_isa_and_triple("x86_64-pc-windows-msvc").unwrap();
    for size in [16, 4080, 4096, 4100, 16384, 16400, 58528, 1048576] {
        let (code, asm) = compile_stack_frame(isa.as_ref(), size);
        // Both unrolled probes and the large-frame loop subtract one page
        // and touch [rsp]. The old bare large subtraction lacks this pair.
        let step = [0x48, 0x81, 0xec, 0x00, 0x10, 0x00, 0x00];
        let touch = [0x89, 0x24, 0x24]; // mov dword ptr [rsp], esp
        if size >= 4096 {
            let step_at = code.windows(step.len()).position(|v| v == step).expect(&asm);
            let touch_at = code.windows(touch.len()).position(|v| v == touch).expect(&asm);
            assert!(step_at < touch_at, "probe must allocate before touching: {asm}");
            assert!(touch_at < 80, "probe must precede local initialization: {asm}");
        } else if size == 16 {
            assert!(!code.windows(step.len()).any(|v| v == step), "small frame needlessly probes: {asm}");
        }
    }
}

#[cfg(target_os = "windows")]
#[test]
fn win64_stack_probe_grows_fresh_thread_stack() {
    use std::ffi::c_void;
    #[link(name = "kernel32")]
    extern "system" {
        fn VirtualAlloc(address: *mut c_void, size: usize, allocation: u32, protect: u32) -> *mut c_void;
        fn VirtualProtect(address: *mut c_void, size: usize, protect: u32, old: *mut u32) -> i32;
        fn VirtualFree(address: *mut c_void, size: usize, kind: u32) -> i32;
        fn FlushInstructionCache(process: *mut c_void, address: *const c_void, size: usize) -> i32;
        fn CreateThread(attributes: *mut c_void, stack: usize, entry: unsafe extern "system" fn(*mut c_void) -> u32,
                        arg: *mut c_void, flags: u32, id: *mut u32) -> *mut c_void;
        fn WaitForSingleObject(handle: *mut c_void, millis: u32) -> u32;
        fn GetExitCodeThread(handle: *mut c_void, code: *mut u32) -> i32;
        fn CloseHandle(handle: *mut c_void) -> i32;
    }
    let (_, isa) = build_aot_isa_and_triple("x86_64-pc-windows-msvc").unwrap();
    for size in [4096, 4100, 16400, 58528, 1048576] {
        let (code, _) = compile_stack_frame(isa.as_ref(), size);
        unsafe {
            let memory = VirtualAlloc(std::ptr::null_mut(), code.len(), 0x3000, 4);
            assert!(!memory.is_null());
            std::ptr::copy_nonoverlapping(code.as_ptr(), memory.cast::<u8>(), code.len());
            let mut old = 0;
            assert_ne!(VirtualProtect(memory, code.len(), 0x20, &mut old), 0);
            assert_ne!(FlushInstructionCache(-1isize as *mut c_void, memory, code.len()), 0);
            // Reserve 2 MiB; commit remains the PE's normal small initial
            // commitment. This tests Windows guard-page growth on a new stack.
            let thread = CreateThread(std::ptr::null_mut(), 2 * 1024 * 1024,
                std::mem::transmute(memory), std::ptr::null_mut(), 0x10000, std::ptr::null_mut());
            assert!(!thread.is_null());
            assert_eq!(WaitForSingleObject(thread, 30000), 0);
            let mut result = 0;
            assert_ne!(GetExitCodeThread(thread, &mut result), 0);
            assert_ne!(CloseHandle(thread), 0);
            assert_ne!(VirtualFree(memory, 0, 0x8000), 0);
            assert_eq!(result, 84, "frame size {size}");
        }
    }
}
