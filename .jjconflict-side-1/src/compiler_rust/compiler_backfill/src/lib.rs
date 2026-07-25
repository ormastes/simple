mod shared {
    use cranelift_codegen::isa::CallConv;

    pub fn platform_call_conv() -> CallConv {
        if cfg!(target_os = "windows") {
            CallConv::WindowsFastcall
        } else {
            CallConv::SystemV
        }
    }
}

#[path = "../../compiler/src/codegen/cranelift_sffi.rs"]
mod cranelift_sffi;
